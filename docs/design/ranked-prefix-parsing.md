# Ranked prefix parsing

The generated ranked-prefix facade returns each selected term with its exact parse cost and complete derivation rank.
The existing `language!` generator emits the facade for every declared category.

## Interface and result policy

The entry point is `parse_<Cat>_via_wpda_ranked_prefix_with_source_and_bounding_mode`.
Its arguments match the existing bounded-prefix facade: token source, completion position, binding power, alternative limit, and cursor bounding mode.

Each result has type `(Cat, ExactParseCost, CompleteDerivationRank)`.
The facade groups results by the generated semantic key.
Each class retains an actual derivation with the smallest cost.
Equal costs select the smallest rank. Equal cost and rank retain the first member.

The facade sorts the retained classes by cost, then rank.
It returns the first requested number of classes.
The completion position identifies the accepted input boundary, including acceptance with trailing input.

A zero alternative limit returns an empty prefix after successful parsing.
Invalid input still returns a parse error.
The ordinary single-result, all-results, and weighted-prefix entry points retain their existing policies.

## Evidence and exact cost

A shared packed parse forest stores completed productions and intermediate grammar steps.
A ranked request retains distinct local weights before forest aggregation can discard their evidence.
Packing identity includes the children, local weight, and positioned lexical decision.
Repeated identical evidence shares one packing.

The existing extractor selects a packing and child coordinates for each occurrence.
Ranked extraction uses those coordinates before semantic deduplication.
Shared forest nodes retain independent choices at separate occurrences.

Each local cost converts to the existing exact tick carrier before addition.
One unit equals 40 ticks. A local grouping cost of 0.025 therefore contributes one tick.
The implementation does not reconstruct exact cost from an accumulated floating-point path weight.
An unrepresentable local cost returns `InexactLocalCost`.

Lexical decisions retain the selected alternative and any opener extent at the consumed input position.
Completed productions contribute their category and rule at the constituent origin.
Intermediate factoring contributes no production authority.

The existing rank representation orders logical input positions first.
At each position, lexical decisions precede production decisions.
Production decisions retain tree preorder.
A longer opener wins at its own position. A later opener cannot replace an earlier lexical decision.

## Bounds and failure behavior

The facade reuses the existing end-of-input driver and selected-occurrence extractor.
It limits each accepted root to 4096 raw derivations.
This is the existing facade realization bound, applied before semantic deduplication.

The extractor must establish exhaustion of its finite family before the facade publishes ranked results.
A root or demanded child that exceeds the bound returns `ResultOverflow`.
The facade does not publish a provisional prefix after that failure.

Cursor overflow, reconstruction faults, action failures, and invalid exact costs remain explicit errors.
The existing traversal and input-step limits also apply.
These bounds limit computation. They do not prove that an omitted reading is invalid.

The ranked facade can examine more derivations than the ordinary weighted-prefix facade.
Complete evidence is necessary because rank can distinguish equal-cost derivations of the same semantic value.

## Algorithm

```text
forest := run the existing driver with packing evidence retention
readings := exhaust each accepted root with the existing extractor
if any root or demanded child exceeds its bound:
    return an error

classes := empty
for each reading:
    class := generated semantic key of the reading
    retain the actual minimum (cost, rank) member of that class

sort classes by (cost, rank)
return the requested prefix and accepted input boundary
```

## Formal model and implementation properties

The facade model extends [FacadeDriverFallThrough.v](../../formal/rocq/prattail_wpda_runtime/theories/FacadeDriverFallThrough.v).
Its `RankedPrefix` module abstracts exact finite costs and total ranks as natural numbers.
The existing [DerivationRank.v](../../formal/rocq/runtime_grammar/theories/DerivationRank.v) supplies cost, composition, position, and factoring laws.

| Formal obligation | Implementation check |
|---|---|
| `choose_is_actual` | `ranked_prefix_retains_actual_minima_and_preserves_the_class_set` checks that each result belongs to the input. |
| `choose_preserves_class`, `retain_preserves_classes` | The same property checks the complete class set and one result per class. |
| `choose_minimum_cost` | The same property compares each class cost with an independent minimum. |
| `equal_cost_selects_minimum_rank` | The same property checks minimum rank among minimum-cost members and stable exact ties. |
| `unequal_cost_ignores_rank` | `lower_cost_dominates_every_rank` varies both competing ranks. |
| `prefix_is_bounded`, `prefix_contains_only_realized`, `complete_prefix_is_all` | The prefix property compares every requested prefix with the complete retained class list. |
| `insufficient_evidence_is_not_success` | `ranked_extraction_requires_complete_evidence_and_retains_equal_values` checks missing evidence and result overflow. |
| `cost_only_aggregation_loses_the_rank_witness` | `equal_cost_requires_the_actual_later_rank_witness` checks the counterexample. The lexical witness test exercises forest aggregation directly. |

The generic prefix properties use 256 cases each.
The packing property also uses 256 cases. It checks evidence identity, exact local weights, reuse, and checkpoint restoration.
The extraction tests check invalid costs, equal semantic values, lexical positions, source-rule traces, and synthetic factoring.

Generated-language tests use the existing LedTest, Class3Opt, and L9ModalToy grammars.
They cover native values, operators, grouping, trailing input, ambiguity, optional collections, binders, and token captures.
The LedTest property uses 64 generated cases.
An independent raw walker oracle checks class sets and minimum primary costs.

These models specify the finite extraction and selection contract.
They do not establish unrestricted termination or equivalence between different parser entry-point policies.

## Generated stack storage

The existing stack gate exposed oversized fingerprint and collection lookup helpers in the generated Rholang parser.
The debug frames measured 243640 and 41080 bytes. Both exceeded the existing 32768-byte limit.

The fingerprint dispatcher now creates one hasher per call.
Only the selected category writes its unchanged tagged stream.
The dispatcher completes the digest once after category selection.
Collection lookup borrows constant records, then copies the selected record once.

The storage refinements preserve the existing dispatch tables and selected values.
[WpdaDispatchPartition.v](../../formal/rocq/runtime_grammar/theories/WpdaDispatchPartition.v) adds three closed obligations for these refinements.

| Formal obligation | Implementation property |
|---|---|
| `shared_digest_preserves_selected_stream` | `generated_digest_preserves_the_exact_selected_stream` compares generated digests with independently generated exact keys across three category types. |
| `shared_digest_preserves_unmatched_input` | The same property checks an unrelated input type after each generated value. |
| `copied_selected_record_preserves_lookup` | `generated_collection_lookup_preserves_the_declared_record` checks all record fields and absent slots against the existing grammar declaration. |

Both storage properties use 128 generated cases.
The stack script includes the ranked facade in its measured symbols.
The DDL test also executes that facade on a 256-KiB thread stack.
The repair does not change either stack limit.

The checks on 2026-10-22 produced these results:

| Build | Measured symbols | Largest frame | Ranked facade frame |
|---|---:|---:|---:|
| Debug | 16270 | 26472 bytes | 5704 bytes |
| Release | 4669 | 4184 bytes | 3256 bytes |

Both builds pass the 32768-byte frame limit.
Both builds execute the ranked facade successfully on a 256-KiB stack.
The complete debug DDL suite passes all 36 tests.

## Focused verification

Run the commands with the repository memory and build-job limits.

```sh
cargo test --locked -p prattail --test ranked_semantic_prefix
cargo test --locked -p prattail --lib ranked_
cargo test --locked -p prattail --lib derivation_rank::tests
cargo test --locked -p languages --no-default-features --features walker-trace --test ranked_prefix_facade --test led_grouped_projection_operand --test l9_modal_toy -- --test-threads=1
coqc -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime formal/rocq/prattail_wpda_runtime/theories/FacadeDriverFallThrough.v
coqchk -silent -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime PrattailWpdaRuntime.FacadeDriverFallThrough
coqc -Q formal/rocq/runtime_grammar/theories RuntimeGrammar formal/rocq/runtime_grammar/theories/WpdaDispatchPartition.v
coqchk -silent -Q formal/rocq/runtime_grammar/theories RuntimeGrammar RuntimeGrammar.WpdaDispatchPartition
scripts/verify-wpda-stack-sizes.sh
WPDA_STACK_PROFILE=release scripts/verify-wpda-stack-sizes.sh
cargo test --locked -p languages --no-default-features --features rholang --test rholang_mettail_ddl ranked_ddl_facade_runs_on_a_256k_stack
cargo test --locked --release -p languages --no-default-features --features rholang --test rholang_mettail_ddl ranked_ddl_facade_runs_on_a_256k_stack
```
