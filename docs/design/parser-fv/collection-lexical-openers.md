# Collection openers in lexical forks

A lexical fork represents several token readings at one input position.
A collection opener starts a collection constructor and establishes its continuation frame.
The parser must preserve that route when another token reading starts at the same position.

## Failure and required behavior

The normal prefix dispatcher already supports collection openers.
The lexical-fork table previously omitted them.
When lexical alternatives consumed different lengths, the normal dispatcher could receive no control.
The fork then contained only the competing routes.

The fixture input `nfold(n,n)` exposes this failure.
Its grammar contains the collection opener `nfold`, the shorter terminal `n`, and an identifier reading.
The incomplete fork could parse the identifier but leave the parenthesis and arguments unconsumed.

The correction adds a collection route to the existing lexical-fork table.
It preserves the existing fall-through conditions.
It adds no token reservation rule and removes no competing route.

## Route construction

Both engine implementations derive collection routes from their existing collection descriptors.
The generated engine uses `classify_collection`.
The owned engine uses the corresponding admitted descriptor row.
Both implementations retain grammar declaration order.

Each `CollectionOpen` entry records the element category and whether the opener requires a separate parenthesis.
The enclosing `LexAltRuleInfo` records the constructor rule.
The shared `collection_prefix::lexical` function constructs the branch.

| Branch component | Required value |
|---|---|
| Marker | The requested category, constructor rule, and collection slot zero |
| Continuation | The caller's binding power |
| Weight | The selected lexical edge's weight |
| Consumption target | The selected lexical edge's target position |
| Direct opener state | Element prefix dispatch at the target, with binding power zero |
| Synthetic opener state | `CollectionOpenParen` with the original owner, rule, element, and continuation |

The branch uses `ConsumeAtAndPush` to consume its specific lexical edge and push its marker.
The walker discards the structural opener as an argument and retains its weight in the parse forest.
The fork itself does not consume a shared trigger.
This distinction permits primary and secondary branches to reach different target positions.

For example, `{|}` must retain the shorter `{` collection opener when the fixture also declares the longer `{|` opener.
The shorter route reads `|` as an element and `}` as the collection closer.
Using the primary edge's target for that secondary route would skip the element.

The synthetic-parenthesis state remains necessary for forms such as `Map(...)`.
Consuming `Map` alone must not permit the parser to omit `(`.
Collection completion continues through the existing collection machinery.

## Formal model and implementation properties

The [collection fork model](../../../formal/rocq/prattail_wpda_runtime/theories/LexForkKeywordReservation.v) contains the `CollectionOpenFork` module.
Its old emission function omits collection routes.
Its corrected emission function retains both collection and ordinary routes.
Its fall-through definition includes the delimiter, branch-count, contextual-keyword, and cross-category conditions used by the implementation.

| Theorem or invariant | Actual implementation test |
|---|---|
| `mixed_length_collection_was_lost` | Before-fix `a_cross_category_bag_fold_fires` regression |
| `mixed_length_collection_is_retained` | `collection_routes_preserve_evidence`, `a_cross_category_bag_fold_fires` |
| `collection_no_loss` | `collection_routes_preserve_evidence` |
| `ordinary_no_loss` | `collection_routes_preserve_evidence` |
| `collection_no_invention` | `collection_routes_preserve_evidence` |
| `rule_order_preserved` | `collection_routes_preserve_evidence` |
| `collection_marker_preserved` | `collection_routes_preserve_evidence` |
| `collection_edge_preserved` | `collection_routes_preserve_evidence`, `secondary_collection_opener_consumes_its_own_edge` |
| `synthetic_paren_is_required` | `collection_routes_preserve_evidence`, opener fixture |
| `direct_opener_starts_element` | `collection_routes_preserve_evidence` |
| `primary_only_uses_normal_dispatch` | `sole_primary_collection_retains_normal_dispatch` |
| `contextual_same_length_keeps_both` | `collection_routes_preserve_evidence` |

The shared-transition property varies categories, rule lists, continuation powers, opener positions, edge targets, and synthetic-parenthesis requirements.
It tests collection openers in both primary and secondary positions.
The property invokes `lexical_fork::prefix` and checks the resulting branches.
The full opener fixture also compares weighted results from generated and owned engines.

The owned action classifier previously rejected every standalone collection.
It now selects one collection input from the existing descriptor.
The input retains its element category and carrier.
The earlier constructor-action branch and the noncollection fallback retain their order.

The `StandaloneCollectionSelection` module in `OwnedCollectionAction.v` proves these selection rules.
Its five theorems map to the implementation evidence below:

| Theorem | Implementation evidence |
|---|---|
| `before_rejects_standalone_collection` | The recorded failing owned-parser comparison before the fix |
| `standalone_has_one_ordered_input` | `owned_collection_actions_preserve_weighted_readings` |
| `binder_priority_is_unchanged` | The same property with `Pair` elements |
| `noncollection_fallback_is_unchanged` | The same property with `Atom` elements |
| `selected_collection_preserves_element_and_kind` | The same property with bag and sequence constructors |

The property varies element counts, delimiters, separators, carriers, and nested constructors.
The provider continues to reject unsupported key/value collection actions.

The proofs establish route preservation and branch metadata.
They do not prove arbitrary grammar correctness or a bound on parser ambiguity.
The integration tests check collection parsing, generated code, and the walker path that consumes the selected edge.

## Verification commands

Run these commands from the repository root:

```sh
cargo test --locked -p prattail --lib collection_open_tests
cargo test --locked -p macros --test prefix_opener_union
cargo test --locked -p languages --no-default-features \
  --features dovetail-codegen,strategies --test collection_fold_carriers
```

Run these commands from `formal/rocq/prattail_wpda_runtime`:

```sh
coqc -Q theories PrattailWpdaRuntime theories/LexForkKeywordReservation.v
coqchk -silent -o -Q theories PrattailWpdaRuntime \
  PrattailWpdaRuntime.LexForkKeywordReservation
```

Use the repository resource limits when running these commands.
