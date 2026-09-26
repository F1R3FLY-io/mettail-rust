# Runtime literal categories and lexical alternatives

Runtime grammars consume the same longest-per-token-kind selection operation as
generated PraTTaIL lexers. The runtime adapter retains a directed acyclic graph
of token edges, indexed by source position and complete lexical-mode context.
It does not replace the generated typed-parser entrypoint or its DFA traversal.

This contract connects three existing layers:

| Layer | Responsibility | Implementation |
| --- | --- | --- |
| Grammar normalization | Bind a decoded literal to its declared category | `grammar-core/src/normalize.rs` |
| Lexical selection | Retain the longest acceptance of each token definition | `grammar-core/src/lexical_selection.rs` |
| Runtime recognition | Follow retained edges with exact mode-context endpoints | `grammar-core/src/runtime/lexical.rs` and `runtime.rs` |

## Literal category membership

A `TokenDefinition` can declare a category, decoder, and native evaluation.
Normalization appends one captured-token rule for each category-tagged token,
after lowering the declared productions. Its `TokenValue` action returns the
already-decoded syntax/value pair unchanged. It adds no constructor, second
decoder invocation, or parse cost. Existing capability checks still authorize
decoding and evaluation.

This rule also exists when the category has explicit constructor productions;
both derivations remain available. Untagged tokens receive no category rule.
Image verification checks the singleton captured-token shape, declared target
category, absent production identity, zero administrative cost, and equality
with the canonical normalized engine.

## Selection is per token definition, not per category

For input `ab`, suppose `Word` accepts `[a-z]+` and `Scalar` accepts `[a-z]`.
The DFA accepts both kinds after `a`, then only `Word` after `ab`. Global
maximal munch would lose the scalar path. The shared selection operation keeps:

| Origin | Kind | Extent | Successor |
| --- | --- | --- | --- |
| 0 | Word | `ab` | 2 |
| 0 | Scalar | `a` | 1 |
| 1 | Word | `b` | 2 |
| 1 | Scalar | `b` | 2 |

Recognition decides which of these edges can inhabit the requested grammar
category. Two different token definitions remain different lexical witnesses
even if they decode to the same value and category. Shorter acceptances of the
*same* token kind are excluded by the declared lexical policy. Consequently,
preservation here is relative to longest-per-kind lexing, not every possible
segmentation of source text.

Acceptances are supplied longest-first; equal-endpoint alternatives retain their
canonical order. The selector performs the following operation without creating
a second edge buffer:

```text
Remember the first supplied endpoint as the local primary endpoint.
For each acceptance endpoint, in supplied order:
    For each accepted token kind, in supplied order:
        If this kind has not survived yet:
            Check the caller's edge budget and emit its unchanged payload.
            Remember this kind and advance the checked alternative ordinal.
    Report this endpoint once if any kind survived there.
On any callback or ordinal error, discard the partial operation and fail.
```

The generated and runtime adapters retain their own DFA, trivia, mode-transition,
and queue policies around this shared operation.

## Full mode contexts are part of parser positions

A runtime position is `(logical input offset, context identity)`. Ordinary
source uses byte offsets; templates count text bytes and one position per hole.
Contexts are immutable
parent-linked frames interned by `(parent identity, mode)`. Comparing only the
top mode would be incorrect:

| Stack, root first | Top mode | Stack after pop |
| --- | --- | --- |
| `[0, 1]` | 1 | `[0]` |
| `[0, 2, 1]` | 1 | `[0, 2]` |

The chart's waiting, completed, nonterminal, terminal, foreign-region, and hole
keys retain these full positions. Child completion requires the exact matching
entry context; source slices, spans, and derivation ranks project only the
logical input offset, with slices resolved inside their text fragment.
Interned frame IDs never become semantic source positions.

The runtime transition contract remains pop-before-push. Popping the root is an
error, including when the same transition also requests a push. Mode depth and
context allocation are bounded before adding a frame. This adapter does not
import the generated parser's different mode-map transition policy.

One iterative queue expands reachable context-indexed nodes. Primary reachability
is propagated only from a primary parent through its locally primary successor.
A node first expanded as secondary may later become primary: reuse its cached
expansion, recheck its stored failure, and propagate its primary successor.

Structural failures confined to a secondary path can refute that path. Resource
exhaustion always fails the request; it cannot turn an incomplete family into a
successful singleton. A structural failure on the primary chain retains the
runtime lexer's hard-error behavior.

## Structural templates, trivia, and foreign regions

Ordinary source and structural templates use this same lattice builder. Text
fragments are not joined: a token cannot cross a fragment boundary or a process
hole. A hole occupies one logical position and creates a typed grammar edge,
never rendered source. It carries the incoming lexical context unchanged.

Primary parser-hidden trivia advances the canonical parser position, including
its declared mode transition. Opaque foreign regions and holes are **not** trivia
aliases: only the corresponding grammar symbol may cross them. Foreign delimiters
are collected once per parse; their payload remains opaque to the host lexer.
Logical end-of-input tokens retain their existing special behavior: one synthetic
position beyond the text, no mode transition, and balanced-context root admission.

## Borrowed lexer and semantic sessions

[`RuntimeLexicalSession`](../../grammar-core/src/runtime.rs) exposes the existing
lexer independently of production recognition. `RuntimeParser::lexical_session`
checks the same input bound and invokes the existing source lexer once;
`lexical_template_session` invokes the existing structural-template lexer once.
The session owns that lattice and borrows the admitted parser and input. It
neither constructs a parse forest nor invokes an alternative recognizer.

| Session operation | Preserved boundary |
| --- | --- |
| `nodes`, `node` | Borrow original nodes and ordered accepted/refuted edges; full `LexPosition` identities include opaque mode contexts |
| `canonical_position` | Follow the original trivia aliases without scanning source again |
| `input_slice`, `hole_at` | Borrow individual text fragments or typed hole occurrences; never join text across a hole |
| `decode_token`, `evaluate_native` | Call the existing decoder/evaluator with unchanged authorization, callback, and capability-revalidation order |

An invalid token ID returns `InvalidToken` before indexing the grammar, copying
input, or invoking a host callback. Valid IDs retain the original decoder
behavior. Native source code remains forbidden, and a revoked capability still
fails after callback revalidation. Input and lexer resource errors are returned
as errors, not as empty candidate sets.

These are adapter interfaces, not evidence of installed-parser cutover. An owned
walker adapter must additionally preserve full position identities, structural
holes, lexical alternative provenance, and balanced end-of-input admission.
The existing parser constructor still performs image verification; obtaining a
session is not a way to bypass it. Focused session tests in `runtime.rs` cover
borrowing, fragment/hole boundaries, malformed token IDs, resource failures,
and capability revocation.

### Owned input view for the shared walker

`OwnedTokenSource::from_admitted_session` connects that session to the existing
`LatticeTokenSource`, which implements the weighted pushdown automaton's input
interface. It does not run a lexer or a recognizer. Its dense node roster retains
the complete `LexPosition` as the inverse identity; two lexer-mode contexts at
the same byte offset remain different nodes. Node zero denotes the original
start after following only the existing trivia aliases.

GrammarCore ABI 6 retains `wpda_token_observations` alongside token IDs. The
producer uses the same active token roster and first-variant selection as the
generated token-to-kind writer. Fixed and custom names are retained payloads,
not a means of guessing a token's family. Boolean token payloads use the original
lexer operation, `text == "true"`; no semantic host callback runs during this
classification. A missing table or binding is an error.

The macro bridge and DDL lowering share
[token declaration projection](../../prattail/src/token_declarations.rs),
including the original built-in-family dispatch, integer-pattern union and
mode-local rules. The token-kind writer observes only declaration names,
payload-type presence and built-in-override flags. Execution priorities,
decoders and mode transitions remain owned by their existing frontend paths;
DDL priorities are not narrowed to the macro priority type.

Declaration order and execution-token order are separate. DDL lowering appends
literal tokens before explicit tokens, while the original first-variant writer
uses declaration order. Each execution-token append therefore carries its
source-position receipt. A missing writer row remains missing; names, regexes
and decoders are not fallback classifiers. The finite receipt laws are in
[TokenDeclarationProjection](../../formal/rocq/prattail_wpda_runtime/theories/TokenDeclarationProjection.v).

Both grammar projections also include the original lexer's implicit structural
terminals: `(`, `)`, `{`, `}`, `[`, `]` and `,`. They borrow the same roster and
retain their existing sorted-set and token-append workers. This matters even
when no authored production mentions parentheses: the original parser supplies
grouping itself. Previously appended declaration IDs stay unchanged; the
sorted literal IDs and grammar fingerprint can change when missing punctuation
is restored. The finite roster and append laws are in
[StructuralTerminalRoster](../../formal/rocq/prattail_wpda_runtime/theories/StructuralTerminalRoster.v);
they do not by themselves prove Rust implementation equivalence.

The current DDL producer covers scalar/object declarations with nonbinding
syntax and explicit, literal or mode-local tokens. It also accepts plain
`List(Base)` parameters with direct separated-list syntax, such as the Regex
theory's `pieces:List(Text)` and `pieces.*sep(",")`. These map to the same
collection-terminal observations as the original macro. The shared collector
retains arbitrary nonempty separators, then applies its original sort and
deduplication; an empty separator contributes no terminal. The execution-token
census and observation producer consume the same collected roster.
[SeparatedTerminalObservation](../../formal/rocq/prattail_wpda_runtime/theories/SeparatedTerminalObservation.v)
states the finite emission laws and their source-correspondence boundary.

Binder, collection-category and other composite source projections are not yet
connected to this producer. Such declarations retain their existing lowering behavior but no
observation table: this owned adapter refuses `MissingTable`, rather than
publishing a partial table as complete. This limitation is distinct from the
generated frontend's existing support for those constructs.

Accepted edges enter the dense view in their original order. Each retains its
token ID, full target position and original alternative ordinal separately from
its dense edge index. Refuted edges remain available through the borrowed
evidence node. Structural holes remain typed occurrences with explicit successor
positions; an empty hole node is not an invented text or end-of-file token.
Logical end-of-input uses the original session predicate, including balanced
mode context and the checked post-EOF boundary. It does not replace root-category
or complete-input coverage checks.

Before constructing the view, `SourceAdapterLimits` admits node and edge counts
and retained string bytes. String accounting includes token-kind payloads and
the original source's lazy secondary cache. Index overflow, resource exhaustion,
missing metadata and invalid positions have distinct error variants. These
adapter limits supplement, rather than replace, lexer and walker work limits.

Category parsing uses `WpdaWalker::new_for_category(engine, category, min_bp)`,
the same entrypoint as generated parser facades. It initializes the category
stack entry and requested result category. `WpdaWalker::new` starts through a
different legacy entry path and is not an interchangeable constructor for this
adapter.

The scoped models
[OwnedLexicalAdapter](../../formal/rocq/prattail_wpda_runtime/theories/OwnedLexicalAdapter.v),
[LogicalEoiObservation](../../formal/rocq/prattail_wpda_runtime/theories/LogicalEoiObservation.v)
and [TokenKindBindingObservation](../../formal/rocq/prattail_wpda_runtime/theories/TokenKindBindingObservation.v)
cover the projection and observation boundaries. Source correspondence and
concrete integration tests remain necessary. This input adapter alone does not
establish installed-parser cutover, complete grammar compatibility, or equality
between the generated and runtime derivation-ranking policies.

### Selected token identity at semantic actions

A token kind and its spelling do not uniquely identify a decoder. For example,
two declarations can accept the same `7` at the same position while declaring
different decoding capabilities. Looking up either declaration by its name,
kind, or text would lose the selected lexical witness.

The owned source therefore supplies the accepted edge's local index. The
existing walker retains it in the shared packed parse forest (SPPF) terminal
key and node, then in `ActionArg::Token`. Cloning, reconstruction and replay into
the action builder preserve this index. Combined with the original source node,
it selects the unchanged `TokenOccurrence`, including its exact `TokenId` and
full-context endpoint. The decoder receives that ID through the existing
authorized `RuntimeLexicalSession::decode_token` worker.

The adapter performs these steps in order:

```text
Read the selected occurrence from the token action argument.
Resolve its exact edge within the original source node.
Check the rule's declared token/category association and source slice.
Invoke the existing decoder once; retain its original error on failure.
Publish the resulting carrier only after the enclosing action succeeds.
```

Missing or invalid occurrence metadata is a protocol error, not permission to
choose a decoder. The original static terminal-interner entry supplies no
occurrence and keeps its original identity equivalence. Recovery-generated
tokens do not acquire an original source-edge identity. These statements concern
identity and callback routing, not a measured performance-equivalence claim.

[TerminalOccurrence](../../formal/rocq/prattail_wpda_runtime/theories/TerminalOccurrence.v)
models unchanged static identity, separation of distinct selected occurrences,
and exact lookup without defaults. Decoder and native-action sequencing is
covered separately by
[OwnedActionAdapter](../../formal/rocq/prattail_wpda_runtime/theories/OwnedActionAdapter.v).
Concrete tests include coincident kind/text alternatives with different
decoders, missing and invalid provenance, and rejection before callbacks.

### Reusing the original transition weights

The owned engine uses the same `LexicographicWeight` and weight constructors as
the generated engine: `lex_one`, `lex_w`, `lex_w_alt`, `lex_w_with_len`, and
`lex_w_alt_with_len`. It forwards the original primary cost, category and rule
indices, lexical-alternative index, and opening-token length at their existing
transition sites. Converting these callbacks to scalar `ExactParseCost` would
erase ranking information; that conversion is not an equivalent adapter.

This reuses the original weighting policy rather than defining a new semiring.
It does not assert that ranking authorizes pruning or that all end-to-end
ambiguity obligations are complete. Actual consumer comparison must check
weights as well as reconstructed terms. The worker-substitution laws in
[TransitionBodyRelocation](../../formal/rocq/prattail_wpda_runtime/theories/TransitionBodyRelocation.v)
apply only when the adapter forwards the same complete observations.

The chain-absorption eligibility query is also shared with the original macro
emitter. Its category, conflict, label and native-literal checks retain their
original order. Every iterative candidate gets an explicit query receipt:
`None` means the original query declined absorption; an absent receipt is an
adapter error. In particular, Regex `PAlt` has no native `Pattern` atom and gets
an explicit `None`. Borrowed query results retain their trigger and separator
text without static leaks. The current owned conversion supports binary results
whose original strings are empty, and explicitly refuses a positive mixfix
result requiring borrowed strings in the runtime's static-string carrier.
[IterAbsorptionObservation](../../formal/rocq/prattail_wpda_runtime/theories/IterAbsorptionObservation.v)
specifies the query and receipt boundary, not a new absorption algorithm.

### Native variable identity

Generated and owned variable actions share the original thread-local variable
cache and its four operations in
[native_variable.rs](../../grammar-core/src/native_variable.rs). The runtime
reexports these operations; relocation does not create another cache or change
its lifetime. Owned actions retain the original first-argument text extraction
and require the declared category to admit variables before invoking the cache.

The dynamic carrier stores the actual `FreeVar` identity and its category in
`DynamicValue::NativeVariable`. This is neither a textual name nor a structural
template hole. Both syntax and value projections retain that identity. The
existing iterative clone, equality, hashing, formatting and destruction workers
handle it as a leaf.

Native identity is process-local and allocation-history-dependent. It is not a
canonical wire identity. Until a checked portable projection exists, portable
`DynamicValue::semantic_key` and serialization reject native variables, including
nested occurrences, with explicit errors. Existing wire tags and encodings remain unchanged. A
publication failure rejects the operation; it must not silently discard the
variable alternative or turn the result into `NoParse`.

Parser-local observational keys are a different interface. The original
generated engine's `semantic_content_key` implements the same byte protocol as
its `semantic_fingerprint`: a result-category tag followed by the generated
semantic visitor. A transparent single-child constructor adds no constructor
tag. In the Regex-shaped macro fixture, `PVar(a)` and `PLiteral(SVar(a))` therefore
have identical parser-local keys, while `PLiteral(StringLit("a"))` has a distinct
key. The original walker retains one weighted representative of the equivalent
variable derivations and the distinct literal interpretation. This is exact-key
equivalence, not rejection based on a top-k limit or merely equal hash digests.

That protocol belongs to the original
[semantic visitor](../../macros/src/gen/term_ops/semantic_hash.rs) and
[walker hooks](../../prattail/src/wpda_walker.rs). An owned adapter must reuse
their source observations and workers, including the original category-local
variant order; a lowered production ID is not a semantic variant tag. Portable
value keys are not a substitute. Parser-local key equality does not authorize
wire publication, prove portable identity, or establish complete ambiguity
preservation outside the compared parser boundary. The generated-consumer
[parity fixture](../../macros/tests/support/owned_engine_parity.rs) checks this
distinction directly, separately from installed-parser activation.

The owned [key adapter](../../prattail/src/wpda_owned/semantic_keys.rs) supplies
the existing result-returning `semantic_content_key` hook. Both realization
paths consult this persistent-key hook before their legacy digest hooks. A
construction or cache-limit error reaches the walker's existing failure latch
and publication barrier; it is not converted to an unavailable key.

The admitted [source roster](../../prattail/src/wpda_owned/semantic_roster.rs)
checks the original category-local variant order, constructor identities, and
ordered source fields against the reduction plan. Its current key profile covers
non-evaluating nullary and regular constructors, unranked transparent projections,
ordered list fields, native string/Boolean/integer literals, and native variables.
It does not infer a folded or native-evaluated constructor's identity from its
syntax. Duplicate labels across categories also leave this profile unavailable:
the original generator's transparent-label observation is global, not per rule.

A source profile outside that checked relation retains the existing no-key
behavior: parser candidates remain available without this deduplication hook.
Sessions containing structural holes also retain no-key behavior, because the
generated AST visitor has no corresponding hole encoding. This decision is made
before key construction; it neither catches a failed key computation nor invents
hole bytes. It is distinct from grammar recognition and portable publication.

[OwnedVariableAction](../../formal/rocq/prattail_wpda_runtime/theories/OwnedVariableAction.v)
covers the shared-worker call, category refusal, identity retention and explicit
publication failure. It does not prove canonical variable projection or general
binder equivalence. Concrete tests check shared cache identity, nested rejection,
and unchanged encodings for the existing value variants.

### Runtime regex character profile

Runtime parser-image compilation selects Unicode-scalar atom semantics, matching
the existing independent image verifier. The original macro compiler entry keeps
its byte-oriented semantics. Both entries use the same regex parser, Thompson
construction, UTF-8 range emission, determinization and minimization workers;
profile selection does not introduce another parser or rewrite user patterns.

The distinction is observable even on valid UTF-8: a byte-oriented dot consumes
one byte, whereas a Unicode-oriented dot consumes one scalar's complete encoding.
Restricting the input to UTF-8 alone would therefore not reconcile the profiles.
Runtime dot, negated classes and shorthand classes use the existing scalar-range
path. Explicit Unicode-property classes already use that path. Unsupported
regex syntax remains an explicit compilation error.

The runtime compiler commitment is `mettail-rtn/5`, so images produced under the
previous character profile cannot silently satisfy the new compiler commitment.
[RegexCharacterProfile](../../formal/rocq/prattail_wpda_runtime/theories/RegexCharacterProfile.v)
proves the profile-selection boundary, not regex-library correctness. The
unchanged independent verifier checks the compiled byte languages; regression
tests separately exercise the original byte entry and runtime Unicode profile.

## Precedence of adjacent operands

A production whose complete syntax is two operands of its own result category is
homogeneous binary juxtaposition. With a declared binding power, it uses the
existing binary precedence comparison, without inventing a terminal or changing
generated token-trigger dispatch flags.

For a parent power `p`, an operand's top production must have greater power;
equal power is additionally allowed on the left for left associativity, on the
right for right associativity, and on neither side for non-associativity.
Atomic operands without a declared power remain admitted. Comparisons avoid
incrementing bounded powers, including at `u16::MAX`. No declared power means
this check imposes no association. Cross-category, binder, collection, and
delimited shapes retain their separate binding contracts.

A grammar declaring `eps` as an epsilon keyword may also admit the literal
sequence `e`, `p`, `s`. Left-associative concatenation removes the right-associated
tree, but does not authorize removing either the epsilon constructor or the
left-associated literal tree. Ranking those two readings is not evidence that one
is invalid. The practical Regex fixture uses `()` for epsilon instead.

### Carrying explicit precedence into shared transitions

Checking completed trees is not sufficient if recognition never constructs the
required tree. Category-leading concatenation uses the original binder route,
not an infix operator with a fabricated empty terminal. For `ab*|c`, a binder
whose right operand always starts at floor zero can construct
`Concat(a, Alt(Star(b), c))`; rejecting that tree afterward does not recover
`Alt(Concat(a, Star(b)), c)`.

The owned adapter therefore supplies checked precedence observations to the
existing operator, category-leading, and binder-parameter transitions. Within
an explicitly ranked category, sorted distinct source powers are represented
by dense entries in the existing byte-sized floor interface:

| Regex operation | Source power | Transition entry |
| --- | ---: | ---: |
| Alternation | 10 | 1 |
| Concatenation | 20 | 2 |
| Quantification | 30 | 3 |

Entry zero remains unrestricted; 255 represents an unranked child. At most 254
distinct explicit levels fit, regardless of the source numbers' magnitudes.
Exceeding that capacity is an explicit error before publishing a table. Adjacent
source powers and `u16::MAX` retain their ordering without source arithmetic.
An equal-power operand uses the parent's entry as its floor; a strictly tighter
operand uses its checked successor. Left concatenation thus parses its left
operand at 2 and its right operand at 3, retaining postfix quantification while
excluding right-nested concatenation and alternation. The original caller floor
is preserved for the continuation. Grouping retains its existing reset boundary.

One original binding-power analysis worker still owns category grouping,
operator order, and descriptor construction. Explicit observations replace
power assignment, not those algorithms. Categories without explicit powers
retain the original declaration-relative arithmetic. Cross-category floor
transport and open mixfix shapes without a checked correspondence are refused,
not assigned a guessed ordinal. The
[explicit-level model](../../formal/rocq/runtime_grammar/theories/OwnedExplicitPrattLevels.v)
proves order transport and admission laws; it does not by itself prove forest
completeness. Actual generated/owned consumer tests remain required.

## Nonassociative postfix declarations

Canonical term declarations accept `"assoc": "left"`, `"right"`, or `"nonassoc"`;
omission retains `"left"`. For a postfix production with a declared `prefix_bp`,
`"nonassoc"` requires the operand's top production to have **strictly greater**
binding power, or no declared power. Left and right settings both preserve the
existing postfix behavior, which also accepts equal power. If the parent has no
declared power, this admission check remains unrestricted for every setting.

The Regex declaration gives its four quantifiers binding power 30 and
`"assoc": "nonassoc"`. Thus `a*?` is rejected, while `(a*)?` is accepted: the
`PGroup` constructor has no declared binding power. This checks the constructor
boundary; it does not inspect parentheses or descend into the group. In bounded
repetition, `PRepeat(Pattern, Nat, Nat)`, only the operand in the result category
`Pattern` supplies this comparison; the ordered `Nat` bounds are unchanged.
Strict comparison requires no increment, even at `u16::MAX`.

The original generated WPDA also supplies constructor-free parentheses. When
the grammar declares `PGroup`, the shared walker retains both interpretations:
`Optional(Star(a))` through the generic grouping boundary and
`Optional(PGroup(Star(a)))` through the authored constructor. Generic grouping
resets the operand's admission boundary without adding a constructor; it does
not authorize erasing an authored `PGroup`. Neither reading may be removed just
because an older parser returned only the authored form. The generated/owned
parity fixture checks both structures and their full weights. The actual Regex
adapter gate separately checks exact authored and generic ground structures;
its old runtime oracle alone cannot establish the complete family because that
oracle also lacks the original implicit-variable alternatives.

The original routing classifier represents `PRepeat` as closed mixfix syntax,
not as a plain unary postfix: its two additional operands retain the following
comma and closing brace. The owned adapter retains that original closed mixfix
route and supplies its checked explicit powers, without changing the canonical
`"nonassoc"` setting or the strict semantic check above. Closure is read from
the classifier's last operand part (or its separate nullary trailing-literal
descriptor), not guessed from source text. Open-ended mixfix routing without
a checked floor correspondence remains explicitly unsupported. The original
declaration-relative admission laws are in
[OwnedPrecedenceAdmission](../../formal/rocq/runtime_grammar/theories/OwnedPrecedenceAdmission.v);
explicit-level transport is covered by the model above.

Admission filters each supplied candidate independently and leaves admitted
syntax, semantic value, parse cost, and derivation rank unchanged. It does not
license selecting the first candidate or treating resource exhaustion as a
syntax rejection. The exact `language_core_to_value` and
`language_core_to_data_fragment` codecs preserve the setting and both grammar and
language fingerprints. The legacy `value_to_presentation` projection is not a
lossless precedence codec.

This setting is implemented for installed runtime grammars. It does not assert
nonassociative-postfix support in generated compile-time parsers or change their
typed-parser hot path.

## Bounds, identity, and verification

| Runtime policy field | Default | Exhaustion code |
| --- | ---: | --- |
| `max_lexer_states` | 1,000,000 | `LexerStates` |
| `max_lexer_edges` | 4,000,000 | `LexerEdges` |
| `max_lexer_work` | 64,000,000 | `LexerWork` |

States count retained positions and persistent mode frames. Edges bound retained
edges/jumps and each node's acceptance scratch. Work counts scheduled node visits,
DFA byte attempts, inspected acceptances, and selected other lexical operations.
It is not a universal CPU meter or a replacement for host-callback limits,
semantic cost accounting, parser-item limits, or forest/result limits.

These limits participate in both installation-policy and symbolic-template-cache
commitments. The runtime compiler ABI is `mettail-rtn/5`; installation policy uses
the `mettail-install-policy/5` domain. Stale executable images are rejected. The
Rholang transport reports lexical exhaustion as `Exhausted`, never `NoParse`.

Formal sources in `formal/rocq/runtime_grammar/theories/`:

- `TokenCategoryNormalization.v`: category binding and unchanged token values.
- `LexicalSurvivorAdapter.v`: selected edges, successor coverage, exact context
  composition, mode/root preservation, failure classification, and reservations.
- `JuxtapositionPrecedence.v`: exact shape recognition and refinement to the
  existing `CategoricalPrattFloor.v` admission predicate; candidate preservation.
- `UnaryPostfixPrecedence.v`: optional parent/child powers, strict nonassociative
  admission, unchanged left/right admission, bounded-power safety, and exact
  supplied-candidate retention, reusing the existing Pratt and filter laws.

These are scoped model/refinement proofs, not a claim that the entire Rust parser
or all end-to-end ambiguity handling has been formally verified. Regression tests
exercise the concrete adapter, including the full-stack counterexample, fragment
and hole boundaries, distinct same-category tokens, policy-sensitive caching,
resource transport, declared associations, and the actual inline Regex module.
Generated-parser performance equivalence requires measurement; sharing selection
code alone does not establish it.
