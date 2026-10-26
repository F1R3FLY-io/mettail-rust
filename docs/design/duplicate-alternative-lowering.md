# Duplicate executable alternatives

Rholang lowering converts parsed alternatives into executable `Par` values.
Two different parsed alternatives can produce the same executable program.
The runtime must execute that program once.

## Defect and correction

Parenthesized names have distinct parser keys, but parentheses disappear during lowering.
The former implementation selected one alternative per parser key and appended every converted program.
Consequently, equivalent alternatives could execute twice.
The regression tests reproduced two outputs instead of one, and four outputs instead of two.

`lower_proc_alternatives_with` now checks each converted program against the retained programs before appending it.
The comparison uses the existing node sorter, `ParSortMatcher`, and `Par::PartialEq`.
Sorting handles parallel components whose source grouping changes their storage order.
The implementation retains the first original program and the original order of alternatives.
It preserves the existing source-key selection and returns the first conversion error.

```text
Parsed alternatives
        |
        v
Existing selection by parser key
        |
        v
Existing conversion to Par
        |
        v
Compare canonical Par values and retain each first original
        |
        v
Append the distinct executable alternatives
```

The equality check compares whole alternatives.
It does not remove repeated processes inside an alternative.
For example, one alternative containing two identical sends still executes both sends.
The implementation does not attempt to prove general behavioral equivalence between different programs.

## Fold contracts

The fold regression exposed a second cause of duplicate execution.
Equivalent alternatives received different fold channel identifiers during combined lowering.
Each alternative produced the same program when lowered separately.

The existing fold allocator now shares a contract across alternatives only when these fields match:

- The fold position in the lowering traversal.
- The fold operation.
- The width or precision.
- The language fingerprint.

Different positions inside one alternative retain different identifiers.
Different operations, widths, and languages also retain different identifiers.
The allocator retains existing descriptors and allocates new identifiers in encounter order.
A single alternative keeps its existing allocation order.
A matching contract can be reused at capacity, but a new contract still returns the existing overflow error.
Each alternative uses one lowering pass.

A local scope owns the allocation table.
The scope resets the position before each selected alternative and clears the table on return or panic.
The scope rejects nested entry and prevents legacy accessors from clearing its descriptors.
Owned lowering sessions retain their existing cleanup of fold descriptors and guard reports.

## Model and properties

The existing [lowering model](../../formal/rocq/rho_bridge/theories/RholangAstLowering.v) now includes parenthesized names.
Its `AlternativeLowering` module models key selection, conversion, duplicate elimination, and assembly.
Natural numbers represent complete source-key identities in the model.
They do not represent truncated hashes.

The model separates conversion and duplicate elimination to state their properties.
The Rust loop performs those operations together and preserves their order.
The equality theorems require an explicit Boolean equality argument that agrees with model equality.
The canonical-comparison theorems accept a canonicalization function as an explicit parameter.
They prove preservation of canonical program membership and retention of the first original program.
They do not prove the node sorter itself.
The Rust properties check the existing sorter and program equality through the actual lowering function.
They do not establish correctness of the entire Rholang interpreter.

The properties generate parenthesis depth, literal values, alternative order, internal multiplicity, duplicate source keys, and conversion failures.
The expected executable programs come from independently constructed integer expressions.
Runtime integration tests additionally execute the output programs through RhoRuntime.

| Theorem | Implementation evidence |
|---|---|
| `exists_ast_exact` | `lowering_alternatives_preserves_distinct_programs_and_internal_multiplicity` |
| `keep_first_membership` | The same property compares the complete assembled program |
| `keep_first_has_no_duplicates` | The same property includes repeated alternatives with different parenthesis depths |
| `deduplication_preserves_exact_program_membership` | The same property checks distinct values and internal multiplicities |
| `distinct_alternatives_are_preserved` | The same property and `ambiguous_term_lowers_every_distinct_proc_alternative` |
| `old_lowering_emits_twins` | Recorded failing runtime tests before the correction |
| `corrected_lowering_emits_one_twin` | The property, the distinct-key premise test, and `ambiguous_parenthesized_names_execute_one_lowered_program` |
| `parallel_duplicates_inside_one_alternative_survive` | The property and `ambiguous_deduplication_preserves_parallel_multiplicity` |
| `failed_lowering_is_rejected` | `alternative_lowering_rejects_failure_at_every_position` |
| `exists_canonical` | Both lowering properties exercise comparison through the existing sorter |
| `canonical_selection_commutes` | `fold_alternatives_preserve_distinct_programs_and_internal_multiplicity` compares canonical output programs |
| `canonical_program_membership_is_preserved` | Both lowering properties check the complete expected programs |
| `canonical_programs_have_no_duplicates` | Both lowering properties vary duplicate alternative order and grouping |
| `canonical_twins_retain_the_first_original` | `canonical_duplicate_comparison_retains_the_first_original_program` reverses parallel components and requires the original result |
| `canonical_comparison_preserves_one_program` | Both lowering properties retain internal multiplicity |

The source-key premise test establishes that parenthesized alternatives have different keys and equal converted programs.
The rejection property also checks that duplicate source keys do not repeat conversion.
It requires conversion to stop at the first error.

The existing [fold model](../../formal/rocq/rho_bridge/theories/HeldFoldContractSound.v) now includes `AlternativeFoldAllocation`.
This model uses complete identity values for operations, widths, and language fingerprints.
Its registry is an ordered list of keys that include the fold position.
The implementation indexes candidates by position and compares their descriptors in the existing site vector.
The `base` parameter represents descriptors allocated before the alternative scope.

| Theorem | Implementation evidence |
|---|---|
| `sequential_allocation_gives_twins_different_indices` | The recorded failing fold-runtime test and isolated-alternative comparison |
| `equivalent_alternative_reuses_the_first_index` | The allocation property and corrected fold-runtime test |
| `lookup_descriptor` | `alternative_fold_allocation_matches_position_and_full_signature` checks each returned descriptor |
| `lookup_append_fresh` | The same property checks new and repeated keys |
| `identical_site_reuses_its_index` | The same property and `alternative_fold_reuse_at_capacity_does_not_allocate_or_alias` |
| `registration_has_the_requested_descriptor` | The allocation property compares operation, width, language, and identifier |
| `registration_preserves_existing_descriptors` | The allocation property checks registry size and previously assigned identifiers |
| `different_site_keys_cannot_alias` | The allocation property compares against an independent map |
| `internal_fold_positions_remain_distinct` | The allocation property and `fold_alternatives_preserve_distinct_programs_and_internal_multiplicity` |
| `different_contracts_cannot_alias` | Both allocation tests vary the contract fields |
| `fresh_registration_is_reused` | The allocation property revisits complete keys |
| `exhausted_fresh_registration_is_rejected` | Both allocation tests check overflow without descriptor growth |
| `registration_index_is_in_range` | The allocation property checks the expected byte index and its overflow result |
| `registration_preserves_capacity` | Both allocation tests check the descriptor count against the independent bounded allocation map |

The fold-lowering property also compares actual programs and contract descriptors against independently selected alternatives.
`held_fold_over_comm_received_value_execs_to_the_folded_value` checks the result through the real runtime.
`ambiguous_fold_contracts_preserve_distinct_outputs_and_multiplicity` checks shared contracts, distinct outputs, and repeated sends through that runtime.
`alternative_fold_scope_cleans_up_and_rejects_reentry` checks cleanup after an error and rejects nested entry.
The formal allocator does not model Rust unwinding or prove the complete fold traversal.

## Verification

Run the Rust checks from the repository root:

```sh
cargo test --locked -p rholang-runtime --no-default-features \
  --config 'profile.test.package.rholang-runtime.codegen-backend="llvm"' \
  --features rholang-runtime,source-oracle --lib rholang_ast:: -- --include-ignored
cargo test --locked -p rholang-runtime --no-default-features \
  --features rholang-runtime,source-oracle --test rho_rholang_ast
```

Run the proof checks from `formal/rocq/rho_bridge`:

```sh
coqc -Q theories RhoBridge theories/RholangAstLowering.v
coqchk -silent -o -Q theories RhoBridge RhoBridge.RholangAstLowering
coqc -Q theories RhoBridge theories/HeldFoldContractSound.v
coqchk -silent -o -Q theories RhoBridge RhoBridge.HeldFoldContractSound
```

Use the repository resource limits for these checks.
