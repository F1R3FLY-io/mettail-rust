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

The Regex fixture's keyword `eps` also admits the literal sequence `e`, `p`, `s`.
Left-associative concatenation removes the right-associated tree, but does not
authorize removing either the epsilon constructor or the left-associated literal
tree. Ranking those two readings is not evidence that one is invalid.

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
commitments. The runtime compiler ABI is `mettail-rtn/3`; installation policy uses
the `mettail-install-policy/5` domain. Stale executable images are rejected. The
Rholang transport reports lexical exhaustion as `Exhausted`, never `NoParse`.

Formal sources in `formal/rocq/runtime_grammar/theories/`:

- `TokenCategoryNormalization.v`: category binding and unchanged token values.
- `LexicalSurvivorAdapter.v`: selected edges, successor coverage, exact context
  composition, mode/root preservation, failure classification, and reservations.
- `JuxtapositionPrecedence.v`: exact shape recognition and refinement to the
  existing `CategoricalPrattFloor.v` admission predicate; candidate preservation.

These are scoped model/refinement proofs, not a claim that the entire Rust parser
or all end-to-end ambiguity handling has been formally verified. Regression tests
exercise the concrete adapter, including the full-stack counterexample, fragment
and hole boundaries, distinct same-category tokens, policy-sensitive caching,
resource transport, declared associations, and the actual inline Regex module.
Generated-parser performance equivalence requires measurement; sharing selection
code alone does not establish it.
