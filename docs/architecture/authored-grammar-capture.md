# Retaining original grammar observations

Parser lowering intentionally discards source structure. For example, a lowered
optional sequence does not retain every distinction between its original binder
context, operation tree, and legacy grammar items. The original macro classifiers
can still inspect those distinctions. Runtime grammars therefore need to retain
the classifiers' inputs, not reconstruct Rust source from the lowered grammar or
implement another set of classification rules.

`AuthoredRuleStore` is that retained input: an owned, flat, typed arena inside
GrammarCore. A production's `authored` field identifies its original rule in the
arena. The arena is structural language data, not executable code, a parser, or
permission to execute a language.

## Source adapters and one shared traversal

The macro adapter borrows the existing `LanguageDef` rule roster before syntax
conversion. The runtime schema adapter borrows decoded, renamed declarations
before production lowering. Neither adapter reparses text. Both supply shallow
observations to
[`capture_authored_nodes`](../../grammar-core/src/authored_capture.rs).

The shared worker uses an explicit heap worklist with `Enter` and `Finish`
frames. On `Enter`, it checks the source identity, obtains one shallow node,
checks admission, and schedules that node's immediate references in field order.
On `Finish`, it resolves completed children, interns the source's name equality
class, and appends a checked owned node. A completed shared child is reused;
duplicate roots still occupy their original positions in the returned roster.
The worker publishes no store when an observation, admission, reference, cycle,
index, or allocation check fails.

All references point backward to already completed nodes. Owned cloning,
serialization, validation, and destruction consequently operate on flat node
storage, without recursively owned child nodes. This does not assert stack
safety for unrelated frontend or parser operations.

The source adapter preserves distinctions that classifiers observe:

| Observation | Retained meaning |
|---|---|
| Context or syntax availability | Absent and present-empty remain distinct. |
| Rule and field order | Original order and duplicate occurrences remain available. |
| Name equality | The adapter uses the source's equality relation; occurrence identity is not name equality. |
| Legacy items | Nonterminal kinds, binder categories, separators, and independently optional delimiters remain explicit. |
| Unsupported observations | A typed unsupported node permits the original classifier to refuse the shape; it does not invent semantics. |

Availability refers to the frontend's model, not to raw optional map keys.
The runtime value schema defaults an omitted term context to `[]`. Both spellings
therefore give a judgement rule a present context, matching the original macro
parser. Ordinary BNF rules have no context; accepted runtime BNF declarations
with nonempty contexts retain and validate those parameters. The macro adapter
separately preserves the actual AST's optional fields, including programmatically
constructed combinations. It does not impose runtime schema defaults on them.

Source identities are temporary memoization keys and are not serialized. Name
equality classes are assigned in deterministic traversal order. In particular,
hash-table iteration order does not select the serialized node or class order.

The macro frontend attaches all incoming rules to one `Arc`-owned store before
conversion. Collection rules synthesized later by that bridge have no fabricated
source reference. The incoming roster may itself contain rules synthesized by
earlier passes: an authored reference describes retained input, not a claim of
human authorship.

## Runtime admission

Untrusted runtime capture reuses the canonical limits and original string-charge
helper. It checks content sizes before copying shallow payloads. Its counters
are:

| Counter | Counted content |
|---|---|
| $`R`$ | Ordered root occurrences. |
| $`N`$ | First shallow node observations. |
| $`E`$ | Immediate typed-reference fields, including duplicate references. |
| $`Q`$ | Elements in retained name, parameter, syntax, and legacy-item vectors. |
| $`B`$ | UTF-8 bytes copied into retained string payloads. |

A reference stored in a vector contributes to both $`E`$ and $`Q`$: these count
different dimensions. The existing node limit bounds $`N`$; the existing item
limit bounds $`R+E+Q`$. Per-string and aggregate string limits bound copied
payloads. These are conservative retained-content limits, not a claim that
capture accepts exactly the same domain as canonical value admission.

The worklist ceiling is derived from admitted content as $`R+N+E`$. The callback
also checks actual memo, store, and name-class lengths before growth. Finishing
moves string payloads and remaps references; it does not charge their content
again. All counter arithmetic is checked. These bounds concern logical lengths,
not allocator capacities, physical bytes, or resident memory.

## Commitments and trust boundaries

The arena affects the grammar commitment because it contains classifier inputs.
It is not diagnostic provenance. GrammarCore ABI 3 and the exact
`mettail-language-core-value/5` envelope require the authored fields to be
present. Explicit unavailability is allowed; silently missing fields are not.
See [identity and compatibility](observation-predicate-roles.md#identity-and-compatibility).

Transport checks typed references and production label/category associations.
Those checks alone do **not** establish agreement between retained observations
and every redundant lowered syntax, classification, or reduction field. Installed
dispatch must consume the shared original derivation as its authority, or check
that correspondence before trusting redundant fields. Retention and transport
alone do not establish runtime parser equivalence or authorize installation.
Declared category and native-literal metadata, and the original
context-to-legacy-item conversion, remain separate inputs to that shared
derivation. The capture worker does not recreate those algorithms or make
their input correspondence automatic.

## Shared descriptor consumers

Retaining observations is useful only when both frontends can feed the original
derivation. The shared [prefix worker](../../prattail/src/wpda_rule_analysis/prefix.rs)
contains the original FIRST traversal: the token predicates with which a category
can begin. It follows category projections through a FIFO queue, skips categories
already visited, and preserves the original order of native, variable, collection,
and declared-rule contributions. The macro adapter still supplies its original
native helpers and Rust token quotation; an owned backend must supply corresponding
observations and predicates, not parse those quotations.

FIRST rows are deduplicated by the original rendered pattern-and-guard key. The
first complete row survives, including its optional guard and provenance flags.
This is preservation of the existing descriptor policy, **not** a proof of
end-to-end ambiguity preservation or permission to truncate parse candidates.
The [FIRST projection model](../../formal/rocq/prattail_wpda_runtime/theories/OriginalFirstSetProjection.v)
proves the finite source-observation substitution and callback order, with the
unfinished state preserved when proof instrumentation runs out of steps.

The shared [grouping worker](../../prattail/src/wpda_rule_analysis/grouping.rs)
likewise retains the original bounded schedule. It collects direct infix and
projection sources, then follows one infix hop from each projection source only
when fewer than four distinct projection sources exist. It is not a transitive
closure. Original category ordering, first-name lookup, narrowing casts, and
callback order remain unchanged; checked runtime index-width admission is a
separate obligation. The [grouping projection model](../../formal/rocq/prattail_wpda_runtime/theories/GroupingSourceDescriptorProjection.v)
covers this exact schedule, including faults and repeated observations.

The original [context-to-items converter](../../grammar-core/src/context_items.rs)
is also shared. It derives the legacy grammar-item roster still observed by the
original classifiers; it does not parse source or infer a context from lowered
syntax. Its outer loop and heap-backed optional-group iterator frames preserve
the original distinction: top-level abstractions emit binder/body items and
binding indices, while abstractions inside optional groups emit only body items.
Partial arrow types retain the original index behavior; this conversion alone
does not validate that every recorded index identifies an emitted item. The
[context projection proof](../../formal/rocq/prattail_wpda_runtime/theories/TermContextItemsProjection.v)
preserves these outputs and observation order. Its input reader is shared with
the existing parameter traversal; the AST adapter is reused by macro generation.

The converter's fallible entrypoint adds admission at the same loop sites; it
does not perform a second traversal. It admits each parameter occurrence before
reading it, each optional frame before growth, each item before construction,
and each binding before allocation. The original AST entrypoint delegates with
infallible admission. A runtime caller must supply a finite policy and shallow,
immutable readers; private output is returned only on success.

Charging occurrences matters even for validated backward-only arenas: two
optional-group references can share a child, and repeated sharing can make a
small arena describe an exponentially large traversal. Arena size alone is not
a bound on that work. The
[context admission model](../../formal/rocq/prattail_wpda_runtime/theories/ContextItemsAdmission.v)
proves budget conservation, first-unpaid-event refusal, and exact successful
publication over the original event schedule. Its trace is mathematical proof
instrumentation, not a trace allocated by the converter. Allocation failure
remains a separate refusal; logical charges do not establish physical memory
usage or the lawfulness of arbitrary constructors.

These workers derive descriptors. They do not recognize guest input, execute
semantic rewrites, or establish that installed parsing already uses the shared
WPDA walker. That integration requires its own transition and consumer checks.

### Native literals, identifiers, and guest modes

The shared [native-literal worker](../../prattail/src/wpda_rule_analysis/native_first.rs)
preserves the original category and declaration lookups. Native-type absence is
different from a present type classified as `Other`. Built-in native families
are selected directly; a custom family additionally requires the first eligible
authored literal declaration with an evaluation body. Runtime adapters must not
infer these observations from a normalized carrier or a generated token name.
The macro adapter retains the original Rust quotations and evaluation payloads.
The [native projection model](../../formal/rocq/prattail_wpda_runtime/theories/NativeFirstDescriptorProjection.v)
covers lookup short-circuiting, ordered pattern/guard construction, and the
distinct home-category and FIRST-set integer policies. It does not prove that a
runtime decoder implements an arbitrary native carrier.

`NativeKind` itself and its original ordered promotion tables live in
[`grammar-core`](../../grammar-core/src/native_kind.rs); AST re-exports that
same enum. The core classifier accepts an already observed last path-segment
spelling, not Rust source. AST retains the original shallow `syn::Type` access
through the `NativeKindFromSynType` extension trait. Rust callers of
`NativeKind::from_syn_type` import both identifiers from `mettail_ast::language`.
No AST dependency, type parser, or new promotion algorithm enters the core.
The [native-kind projection model](../../formal/rocq/prattail_wpda_runtime/theories/NativeKindProjection.v)
preserves the original classifier, tables, and queue behavior; it does not prove
that the tables' numeric embeddings or runtime decoder implementations are valid.

The prefix worker also contains the original identifier summaries: whether a
category has a home variable reading, which categories have an identifier FIRST
contribution, and whether a source's identifier readings are variable-only.
The latter uses explicit category/rule frames and the original pure-projection
test; it is not unrestricted transitive delegation. The
[identifier projection model](../../formal/rocq/prattail_wpda_runtime/theories/OriginalIdentSummaryProjection.v)
preserves that existing decision procedure, including its ordered legacy-item
reads and cycle handling. This is not a new justification for parse pruning.

The shared [guest-mode worker](../../prattail/src/wpda_rule_analysis/guest.rs)
selects the first matching opener token, then its pushed mode, then that mode's
tokens which push the same mode. A missing push on the first matching opener
does not cause a search for a later duplicate. Returned opener names retain
order and duplicates. Token-name matching, mode-name equality, and output-name
rendering remain distinct operations, as captured by the
[guest projection model](../../formal/rocq/prattail_wpda_runtime/theories/GuestModeDescriptorProjection.v).
For example, identical rendered mode names cannot substitute for source name
equality. An owned adapter must retain that equality rather than strip
qualifiers from lowered lexer names.

## Verification boundaries

The Rocq models separate obligations rather than treating an interface test as
an end-to-end proof:

- [Store projection](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredRuleStoreProjection.v)
  specifies typed postorder references and owned-reader observations.
- [Capture projection](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredRuleCaptureProjection.v)
  specifies the shared worklist, identity reuse, root order, and failure boundary.
- [Transport projection](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredRuleTransportProjection.v)
  specifies owner association, field forwarding, and exact-format commitments.
- [Runtime admission](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredRuntimeCaptureAdmission.v)
  derives logical-size bounds using the existing work-budget and capture models.
- [Schema context projection](../../formal/rocq/prattail_wpda_runtime/theories/SchemaAuthoredContextProjection.v)
  preserves runtime default-key equivalence while distinguishing it from the
  macro adapter's raw optional-field contract.

Concrete source-adapter tests remain necessary to connect each frontend to these
models. These proofs do not establish hash injectivity, arbitrary callback
lawfulness, physical allocator behavior, or completeness of the original parser.
