# Constructor reconstruction at the DDL boundary

## Scope

Rholang's generated parser reads inline Module/Theory declarations structurally.
Reconstruction turns a selected derivation in its shared packed parse forest
(SPPF) into the typed Rholang syntax tree. It must preserve the selected
constructor, operand occurrences and collection contents before DDL elaboration
produces the canonical language value. It must not parse the theory text again.

This checkpoint combines the existing occurrence-reconstruction support with a
candidate-local constructor decision. Those changes share internal slot types,
action frames and failure transport; they are one coherent implementation
snapshot. They do not establish complete end-to-end ambiguity preservation,
global heap minimality, a fully resumable parser, or universal resource bounds.
The remaining general obligations are not discharged by the Regex fixture.

See [runtime lexical selection](runtime-lexical-lattice.md) for the separate
typed-literal/category connection and guest-parser lattice. This document
concerns the generated host parser's reconstruction, not a second guest parser.

## The demonstrated constructor failure

In the inline Regex theory, `(PFail)` on an equation's right side could be
recognized both as an explicit constructor and as a grouped variable. Both
readings existed in the forest. A longer left-side constructor masked their
length difference in the enclosing comparison:

```math
\max(7,5) = \max(7,0).
```

Their other earlier comparison fields also tied in the concrete witness.
The explicit collection-bearing constructor had no retained-wrapper decision,
so packing discovery order could choose the variable reading. Canonical theory
validation then correctly rejected `PFail` as an unbound right-side variable.
Changing that validator or treating `PFail` specially would not repair the
earlier reconstruction error.

The shared walker now extends its existing retained-wrapper decision using
the rule's declared leading structural trigger and the **selected** flat's
collection presence. Empty collections still count as present. It adds one
decision when either the historical one-symbol case or the new collection case
applies; declared coercions remain excluded. No constructor name, language name
or Regex-specific branch is involved.

## Selected occurrences, not shared-node guesses

A shared forest node can occur several times in a parent. Each occurrence has
its own selection coordinate. Reusing a node identifier must not collapse those
coordinates or replace the selected entry with the first raw entry.

For example, two occurrences of a shared node with two alternatives have four
ordered combinations:

| First occurrence | Second occurrence |
|---|---|
| A | A |
| A | B |
| B | A |
| B | B |

The existing explicit reconstruction worklist and source-ordered Cartesian
cursor carry these occurrence coordinates. The cursor does not allocate the
whole Cartesian product. Zero rows yield one empty coordinate; an empty row
yields no coordinate. Equal values do not make two occurrences the same slot.

For constructor evidence, each selected intermediate fragment stores a Boolean
projection of its flat: whether that exact flat contains a collection. Direct
collection leaves contribute presence. Selected intermediate fragments contribute
their cached projection. Symbols and optional packing boundaries remain opaque.
The scan validates every selected coordinate, even after presence becomes true.
Missing coordinates or malformed arity are reconstruction errors, not absence
of a constructor.

This is the projection algorithm, expressed without reconstructing another AST:

```text
Check that the selection vector has exactly one coordinate per slot.
Inspect direct children for collection leaves; reject missing forest nodes.
For each slot and its selected coordinate:
    Require the corresponding selected entry to exist.
    For an intermediate fragment, combine its cached presence.
    For a semantic symbol, preserve the opaque boundary.
    Reject an incompatible slot/value shape.
Return the combined presence only after all coordinates pass.
```

## Action ownership and failure transport

`SelectedCollection` owns an immutable ordered slice containing only terms or
the explicit absent-value marker. It cannot contain another selected collection
or an unresolved accumulator reference. Immediately before a reconstructed
semantic action runs, an action-local frame assigns its collections fresh slots.
Each slot is drained at most once, independently of parser accumulator state.

Generated collection conversion is all-or-error. A mismatched element cannot be
silently removed by `filter_map`, leaving an apparently valid shorter collection.
The existing generated semantic actions remain responsible for constructing the
typed terms; the frame does not introduce another evaluator.

`RealizationError` distinguishes semantic-key resource failures, invalid
reconstruction and action-protocol failures. A failed realization request
discards its provisional output and retains the failure cause. It does not
declare the source invalid, an incomplete family empty, or a surviving candidate
unique. Stack-safe action-argument lifecycle handling includes the closed
selected-collection payload.

The implementation lives in
[wpda_walker.rs](../../prattail/src/wpda_walker.rs),
[action_collection_frame.rs](../../prattail/src/wpda_runtime/action_collection_frame.rs),
[cartesian_cursor.rs](../../prattail/src/wpda_runtime/cartesian_cursor.rs) and
[realization_error.rs](../../prattail/src/wpda_runtime/realization_error.rs).

## Formal correspondence and its limits

[ConstructorElectionEvidence.v](../../formal/rocq/prattail_wpda_runtime/theories/ConstructorElectionEvidence.v)
proves the selected-flat Boolean projection, the exact new eligibility condition,
preservation of previous candidate values and earlier rank fields, and insertion
of the observed ordinal-zero decision under a common ordered context. It does
not prove that every ordinal improves rank, or that a bounded k-best prefix is
complete. The concrete producer/consumer relation still needs regression tests.

The accompanying occurrence, collection-assembly, selected-plan, failure-boundary,
Cartesian-cursor, continuation and lazy-packing models describe the supporting
representation and control transitions. The retained-family scheduler model
and reconstruction-work-budget model also preserve future proof obligations;
including their sources does not assert that all corresponding production
scheduling and metering work is implemented. Model theorems and Rust correctness
are distinct claims.

The generated DDL regression suite checks recursive and right-side nullary
constructors, complete Module/Theory declarations, legitimate variable readings,
and the actual Regex fixture. The k-best tests check reversed packing insertion,
selected intermediate coordinates, opaque boundaries, malformed coordinates,
coercion exclusion and one decision when both eligibility cases apply. These
checks retain the existing Weight and FirstRaw test families.

## Reproducing the focused checks

The checkpoint's local regression results are:

| Check | Passing cases | Boundary exercised |
|---|---:|---|
| Generated Rholang DDL | 27 | Structural declarations, constructor election and lexical domains |
| Runtime language installation | 67 | Real Regex fixture, atomic images, identities and capability controls |
| K-best reconstruction | 42 | Selected occurrences and constructor evidence |
| Indexed action frames | 12 | Independent slots, protocol failures and deep optional groups |
| Cartesian cursor | 6 | Ordered products, resumption, checked width and small-stack traversal |
| Optional assembly | 8 | Occurrence products, weights and failure publication |
| Weighted preparation | 6 | Shared nodes, cycles, missing dependencies and deep traversal |
| Exact collection conversion | 3 | Order, repeated occurrences and all-or-error conversion |
| Parse-error lifecycle | 4 | Failure causes and depth-20,000 clone/format/drop behavior |

All twelve accompanying proof modules were compiled and independently checked
by the Rocq kernel checker. Their selected assumption reports were closed under
the global context. This verifies the stated models, not an extracted or
machine-checked refinement of the complete Rust implementation. A separate
source review checked the local model/implementation correspondence; it did not
execute the tests independently or discharge the deferred general obligations.

Run one heavy command at a time. Keep scratch files, logs and proof artifacts
under `target/`; use one Rust build job and no swap. The current local checks use
an 8 GiB hard Rust limit and a 1 GiB hard Rocq limit.

```sh
mkdir -p target/test-tmp target/verification/constructor-checkpoint
systemd-run --user --scope --quiet \
  -p MemoryMax=8G -p MemoryHigh=7680M -p MemorySwapMax=0 \
  env CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 TMPDIR="$PWD/target/test-tmp" \
  cargo test --locked --offline -p prattail --lib kbest_ -- --test-threads=1
systemd-run --user --scope --quiet \
  -p MemoryMax=1G -p MemoryHigh=900M -p MemorySwapMax=0 -p TasksMax=8 \
  coqc -q -Q target/verification/constructor-checkpoint PrattailWpdaRuntime \
  -o target/verification/constructor-checkpoint/ConstructorElectionEvidence.vo \
  formal/rocq/prattail_wpda_runtime/theories/ConstructorElectionEvidence.v
systemd-run --user --scope --quiet \
  -p MemoryMax=1G -p MemoryHigh=900M -p MemorySwapMax=0 -p TasksMax=8 \
  coqchk -silent -Q target/verification/constructor-checkpoint PrattailWpdaRuntime \
  PrattailWpdaRuntime.ConstructorElectionEvidence
```

Use the same Rust resource wrapper for these additional test commands:

```sh
cargo test --locked --offline -p languages --no-default-features \
  --features rholang,rho-codegen,dovetail-codegen \
  --test rholang_mettail_ddl -- --test-threads=1
cargo test --locked --offline -p rholang-runtime --no-default-features \
  --features rholang-runtime --lib language_install::tests -- --test-threads=1
cargo test --locked --offline -p prattail --test parse_error_lifecycle \
  -- --test-threads=1
```

The remaining library filters are `indexed_action_frame_`, `cartesian_cursor_`,
`optional_assembly_`, `weighted_preparation_` and `exact_collection_conversion_`;
substitute each for `kbest_` in the capped library command above. These are
focused regressions, not the complete workspace suite. Generated-code and
floating-toolchain warnings remain visible; passing tests do not establish a
warning-free build or compatibility with a future compiler.

The focused strict Clippy command (`-p prattail --lib --test
parse_error_lifecycle --no-deps -- -D warnings`) failed with 318 library
diagnostics. All reported primary locations were outside this checkpoint's
added or modified line ranges; none named the new support modules. This
source comparison is not a separate baseline compiler run. The strict-lint
gate remains open, and no warnings were suppressed to obtain a passing result.

The full inline installation test additionally requires the explicit node
dependency snapshot. Local path relocation is not a release pin. Record its
actual commit and the MeTTaIL source snapshot; do not weaken a revision checker
or silently mutate another worktree to make the check pass. The generated parser
fixture and a library installation test are not the actual node/FLT application
demonstration.
