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

### Source declarations and final lexer bindings

The optional `AuthoredDeclarations` header retains category names, original
`NativeKind` observations, collection delimiters, token declarations, and named
mode rosters. Token rows are ordered global declarations first, then each mode's
declarations. Concatenating those rosters must give every source token position
exactly once. Duplicate declaration payloads remain distinct positions.

[`capture_authored_declarations`](../../grammar-core/src/authored_capture.rs)
appends category, token, and mode name occurrences after the rule roots and
invokes the same capture controller once. These names therefore share the
rule capture's identity memo and source-equality classes. The returned rule
positions do not change, and a zero-rule language can still retain declarations.
An explicit `LanguageSpec` owner preserves that zero-rule case through the
macro bridge; present rule owners must agree with it.

Source positions are not lexer token IDs. For example, several integer
declarations can share one built-in token; a rational declaration can produce
both a custom token and a typed-literal token. The separate
[`AuthoredDeclarationBindings`](../../grammar-core/src/authored_bindings.rs)
table records these actual lowering results. It never guesses them from token
names or normalized native carriers. Its private builder accepts each assignment
once; an explicitly absent auxiliary route is distinct from an unfinished slot.
Publication requires exact source/table cardinalities, matching category
spellings, valid token and mode IDs, and membership of both token routes in
their recorded modes.

This validation establishes structural associations, not decoder equivalence
or authority. The macro bridge records original builtin-selection outcomes and
typed-pattern insertion provenance at their existing source sites. Runtime
schema lowering also records IDs at its existing append sites. Its source
header lists explicit global tokens, literals, then mode tokens; its execution
order remains literals, explicit globals, then mode tokens. For example, one
explicit token and one literal occupy source rows 0 and 1, but their direct
IDs are 2 and 1 because the implicit `Identifier` occupies execution ID 0.
Source rows exclude implicit identifiers and synthesized terminal tokens.

The schema retains each scalar's native observation before lowering erases
width information. Canonical `BigRat` and `Fixed` map to the existing canonical
native kinds; other scalar symbols use the unchanged original classifier.
An omitted carrier remains absent, while collection and external carriers have
the original opaque `Other` observation. Their richer canonical `Carrier`
values remain separate. Literal names use the original first-match selector
once, with borrowed names until ordinary name capture copies them.

The [owned declaration reader](../../prattail/src/wpda_rule_analysis/authored_declarations.rs)
requires the store, declaration header, and binding table, then applies the
existing full GrammarCore validator and authored-rule reader checks. A missing
header is unavailable input, not an empty declaration roster. The reader borrows
the immutable owner; it does not reconstruct a source AST or confer installed
language authority. Installed-parser integration remains a separate obligation.
Neither retained observations nor final-ID bindings establish native decoder,
value, or arbitrary Rust-wrapper equivalence.

The reader feeds these retained fields directly to the existing category census,
native-literal selectors, and guest-mode worker. An external rule roster is
checked completely before census dispatch; its order and duplicate entries are
passed through unchanged. The caller must supply the original source roster,
not add later synthetic rules. Literal selection returns a source position;
looking up its binding is a separate operation. Guest opener matching uses the
retained spelling, while pushed-mode matching uses retained name-equality
classes. Thus `r#Open` is not silently treated as `Open`, and matching displayed
mode names do not override the source's equality relation.

Category roles use the existing producer relation
`admits_variables = !is_data` through the checked category binding. Missing
source rows return no role rather than guessing. The low-level census callbacks,
like the original rule-reader callbacks, require handles from the validated
owner; the checked census entrypoint validates externally supplied rule IDs.

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
| $`W`$ | Declaration-row and literal-selector work plus original context-conversion event charges. |

A reference stored in a vector contributes to both $`E`$ and $`Q`$: these count
different dimensions. The existing node limit bounds $`N`$; the existing item
limit bounds $`R+E+Q+W`$. Per-string and aggregate string limits bound copied
payloads. These are conservative retained-content limits, not a claim that
capture accepts exactly the same domain as canonical value admission.

The worklist ceiling is derived from admitted content as $`R+N+E`$. The callback
also checks actual memo, store, and name-class lengths before growth. Finishing
moves string payloads and remaps references; it does not charge their content
again. All counter arithmetic is checked. These bounds concern logical lengths,
not allocator capacities, physical bytes, or resident memory.

For judgement rules, the schema adapter invokes the original context converter
once after precharging the rule node. Parameter visits, optional frames, and
item construction each add one unit to $`W`$; each binding adds two. A generated
legacy item adds one reference to $`E`$ and one vector element to $`Q`$, but no
new rule node. Names remain borrowed until ordinary name capture; actual
separator copies pass the original string gate before construction. Bindings
are still constructed and charged even though this retained projection keeps
only the item roster. BNF copying and context presence are unchanged. The
[schema converter model](../../formal/rocq/prattail_wpda_runtime/theories/SchemaContextItemsProjection.v)
composes these checks with the original finite execution and capture bounds.

Declaration capture prepays the contents of the header, its remapped row
vectors, and the pending and finalized binding vectors. It includes every
declaration-name occurrence in the combined root count before allocation.
Collection-delimiter strings pass the same string gate before copying. Each
literal prepays a category-count upper bound before calling the original
first-match selector; context conversion adds to this work rather than resetting
it. The [schema declaration model](../../formal/rocq/prattail_wpda_runtime/theories/SchemaDeclarationCaptureProjection.v)
connects these counts to the actual vector phases and source/execution roster
positions. This is conservative logical-content admission, not allocator or
instruction accounting.

## Commitments and trust boundaries

The arena affects the grammar commitment because it contains classifier inputs.
It is not diagnostic provenance. GrammarCore ABI 4 and the exact
`mettail-language-core-value/6` envelope require the authored fields to be
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

### Legacy rule normalization

The original [legacy rule normalizer](../../ast/src/legacy_rule_normalization.rs)
converts supported BNF item rosters into a term context and syntax pattern. It
first refuses rules that already have either field, then scans for unsupported
nonterminal kinds before its original forward construction pass. Pending
binders, generated parameter names, fixed collection names, and every original
semantic refusal retain their existing order. It does not parse source or
reconstruct a Rust AST.

`try_normalize_legacy_rule_with` adds admission inside those same two loops.
It checks each item visit before reading the item, and each construction site
before argument clones, string copies, output reservation, or construction.
The original static entrypoint delegates with an always-accepting policy.
No extra scan or runtime event log is allocated. Output vectors reserve their
next slot fallibly; the fresh-name counter is checked before its constructor.
The policy must separately cover the actual shallow adapter costs.

`Ok(None)` means the original normalizer refused the shape; it is not a resource
error. Admission, reservation, and counter failures return distinct errors.
Neither refusal nor error returns a partial context/syntax pair. Constructors
must stage any effects privately; this interface alone cannot enforce that law
for arbitrary adapters. The [admission model](../../formal/rocq/prattail_wpda_runtime/theories/LegacyNormalizationAdmission.v)
composes the original normalization proof with checked debit and prefix laws.
The [adapter tests](../../ast/tests/legacy_rule_normalization_adapter.rs) check
the original output/callback fixtures and denial before each of 40 reached sites
in a mixed binder, literal, and collection fixture.

The [owned normalization adapter](../../prattail/src/wpda_rule_analysis/authored_normalization.rs)
consumes one validated `AuthoredRuleStore` in constant time. It records the
original arena length and accepts only original rule handles during that
session. It calls the shared normalizer once. Its constructor callbacks stage
fixed-depth parameter and syntax recipes, keeping fallible arena effects outside
those callbacks. A semantic refusal returns the original handle without building
a name index. An error consumes the private session and returns no partial store.

On successful normalization, the adapter lazily indexes source names. This
adapter supports the original producers' profile: equal spellings correspond
exactly to equal source classes. It checks both directions without strengthening
the generic arena invariant or renumbering existing classes. Original names and
nodes remain untouched. Generated `p0`, `p1`, and `elems` spellings reuse an
existing representative when present; otherwise a checked class above the
current maximum is added. Raw `r#p0` remains distinct from `p0`. A hit at the
maximum class succeeds; only a required extension can overflow. Hash-table
iteration never determines node IDs, representatives, or class numbers.

Materialization proceeds as follows:

1. Admit and reserve each known-length output roster once.
2. Resolve generated names and append the original constructors' shallow child
   nodes before their owners: base/arrow/collection types and parameters, or
   source-free separator operations. Every collection kind retains the original
   single-element `Collection` representation, including Map and PathMap.
3. Admit each original legacy-item payload before copying it.
4. Append complete parameter and syntax rosters, then one new rule retaining the
   original label, category, and legacy items. Publish the session and new handle
   together. Existing rules and the declaration header are never overwritten.

Independently optional collection delimiters are checked at the reached original
preflight item. A half-present pair is unsupported; both absent retain the
original semantic refusal, and present empty strings remain present. Existing
context/syntax presence gates run first. There is no preliminary grammar scan
that changes this refusal order.

The [materialization model](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredNormalizationMaterialization.v)
connects the concrete recipes, name-index reads and class extension, checked
append, original-handle boundary, and final publication. Derived name IDs may
reuse representatives: the claim is spelling/equality and reader correspondence,
not identical occurrence IDs or serialized bytes from a separately recaptured
AST. The [adapter tests](../../prattail/src/wpda_rule_analysis/authored_normalization/tests.rs)
exercise these positive and refusal boundaries. Callers still supply finite
admission policies covering actual copies, indexing, and construction. Logical
admission is not a physical memory guarantee or a proof of arbitrary callback
behavior; this adapter alone does not activate installed parser generation.

These workers derive descriptors. They do not recognize guest input, execute
semantic rewrites, or establish that installed parsing already uses the shared
WPDA walker. That integration requires its own transition and consumer checks.

### Atomic prefix rows

The shared [atomic-prefix worker](../../prattail/src/wpda_rule_analysis/atomic_prefix.rs)
consumes the existing atomic classifier's descriptor; it does not classify the
rule again. Six leaf cases request the original token predicates. A patterned
literal delegates once with the original home-category policy and retains every
returned row, guard, duplicate, and position. Projection, prefix-unary,
prefix-operator, multi-literal nullary, and non-atomic shapes emit no atomic rows;
their existing dispatch paths remain responsible for them.

The same module owns the original unified prefix descriptor vocabulary, with
opaque token payloads instead of a dependency on Rust token quotation. The macro
adapter still supplies those quotations. The shared left-binding-power lookup
also preserves the first operator row satisfying the original label, result,
and source-category comparisons. The
[atomic descriptor model](../../formal/rocq/prattail_wpda_runtime/theories/AtomicPrefixDescriptorProjection.v)
proves callback order and row/field preservation. It does not cover the surrounding
multi-pass bucket driver or transition execution.

The surrounding [prefix-bucket driver](../../prattail/src/wpda_rule_analysis/prefix_bucket.rs)
is shared separately. It preserves the original schedule: cross-category
sources, first local classification pass, delayed atomic-row insertion, then
the second local classification pass. Global authored rules and indexed local
rules remain separate rosters; the latter can contain synthesized rules.
Classification is repeated at the original second-pass sites, not cached.
The existing lexical-compatibility checks retain their per-row short-circuit
order. The [driver projection model](../../formal/rocq/prattail_wpda_runtime/theories/OriginalPrefixBucketDriverProjection.v)
proves finite callback and descriptor correspondence. Rust transition emission
remains in the original backend and is outside this model's claim.

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

The original [literal-name selector](../../grammar-core/src/literal_name.rs)
also uses the shared native-kind table. It inspects only the first category
equal to the original literal name, even if that category has no native type.
A standard token variant is constructed with the original literal occurrence's
span; otherwise the original name is cloned. The AST keeps those constructors,
its surrounding declaration validation, and its token metadata moves. The
[literal-name model](../../formal/rocq/prattail_wpda_runtime/theories/LiteralNameProjection.v)
preserves this lazy lookup and constructor schedule without assuming that name
equality is spelling equality or defining a new runtime carrier policy.

Constructor labels use a different existing classification:
[`NativeType`](../../grammar-core/src/native_type.rs) retains all 25 original
code-generation variants, including collection wrappers and `Other(String)`.
It is not a replacement for `NativeKind`. The macro keeps its shallow
`syn::Type` probes through `NativeTypeFromSynType`; the shared core receives
their observations rather than parsing or reconstructing Rust types.

The shared [label helpers](../../grammar-core/src/constructor_labels.rs) keep
the byte-vector probe first. A byte-vector result selects `BytesLit` without
calling native classification. Otherwise the original integer test and native
match select the label, including the ordered `HashSetLit` and `PathMapLit`
opaque-name cases. The selected constructor is called once. Variable labels
use the first Unicode scalar's full uppercase expansion, followed by `Var`;
they do not truncate that expansion to one byte or character. For example,
`ßuffix` produces `SSVar`.

The [constructor-label model](../../formal/rocq/prattail_wpda_runtime/theories/ConstructorLabelProjection.v)
preserves the lazy observation and constructor schedule. Its scope is label
selection, not decoder equivalence, serialized native metadata, allocation
failure, or arbitrary callback correctness. The
[original-behavior fixtures](../../macros/tests/support/constructor_label_baselines.rs)
check the actual macro helpers, including qualified types, unsupported shapes,
byte-vector argument gates, raw identifiers, and Unicode expansion.

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
- [Extended capture composition](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredExtendedCaptureComposition.v)
  checks the same finite-run controller with both arrow children and the
  multi-binder child retained. Ordered declaration-name roots use that same
  capture run and name table. Concrete adapters must separately establish their
  correspondence to those source observations.
- [Declaration binding](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredDeclarationBindingProjection.v)
  separates immutable source rows from write-once final-ID association and
  checks complete token-roster coverage before publication. It does not infer
  the provenance of an arbitrary supplied ID.
- [Declaration reader](../../formal/rocq/prattail_wpda_runtime/theories/AuthoredDeclarationReaderProjection.v)
  composes existing validation results with ordered rule checks, original
  census/native/guest worker substitution, source-position lookup, and the
  category-role producer relation. It does not reprove the Core validator or
  establish runtime resource admission. The [reader tests](../../prattail/src/wpda_rule_analysis/authored_declarations/tests.rs)
  exercise these boundaries with validated fixtures, nonidentity final token
  bindings, duplicate source rows, raw names, and rejection cases.

Concrete source-adapter tests remain necessary to connect each frontend to these
models. These proofs do not establish hash injectivity, arbitrary callback
lawfulness, physical allocator behavior, or completeness of the original parser.
