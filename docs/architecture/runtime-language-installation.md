# Runtime language installation

## Boundary and ownership

Inline `Module` and `Theory` declarations are process forms in the generated
[Rholang grammar](../../languages/src/rholang.rs). The application parser
produces their structural syntax once. The
[DDL lowerer](../../rholang-runtime/src/ddl_ast.rs) transports that structure;
the installer does not extract theory text and invoke another textual parser.
Programmatically constructed canonical language values enter the same
elaboration and installation path.

[LanguageInstallService](../../rholang-runtime/src/language_install.rs) owns
the host-facing operation. It consumes an injected immutable registry snapshot
and explicit host policy. Registry lookup supplies definitions and commitments,
not authority. Filesystem loading remains unavailable until an injected File
I/O capability implements that boundary; installation does not read ambient
files.

`LanguageCoreV1` contains syntax and theory projections. The grammar fingerprint
identifies syntax/parser inputs; the full-language fingerprint also commits to
the theory. Equal grammars with different theories may reuse a compatible
parser artifact, but must not share a full-language identity or acquire each
other's rights. This is an identity/cache contract, not a promise of physical
memory deduplication.

## Prepare, admit, publish

The phases have distinct mutation boundaries:

| Phase | Work | Publication |
|---|---|---|
| Canonicalize | Resolve the fixed registry snapshot and structurally elaborate each export | None |
| Check requested authority | Reject unavailable checker requirements and actions whose required rights are absent from the requested manifest | None |
| Derive artifacts | Reuse admissible caches or compile parser and executable theory images from the canonical language | None |
| Apply host policy | Attenuate requested rights against host grants, assemble capability-bound install requests, and enforce the installed-language limit | None |
| Admit the complete batch | Verify every image and commitment; preflight conflicts and entry allocation | None until the whole batch is admitted |
| Commit and return | Publish the batch, retain its revocation authorities, and return opaque handles and ordered staged programs | One installed-table batch commit |

The production implementation reuses `compile_parser_image`,
`compile_theory_semantic_image`, and
[InstalledLanguageTable](../../grammar-core/src/installed.rs). It does not
introduce another grammar compiler or semantic evaluator.

`commit_batch` preflights the complete request before mutating the installed
table. A valid first export followed by an invalid second export must not
publish the first one. The service holds its revocation-map write lock while
checking the resulting language count, invoking the table commit, and retaining
the returned revocation authorities. The two maps are not one storage object;
the regression checks compare both after returned failures and successes. They
do not establish a general cross-lock linearizability proof or recovery from
process aborts and allocator termination.

Staged module programs remain ordered data until installation succeeds. Their
later execution, metering and rollback belong to the host execution boundary;
installation success alone does not execute a module's subprograms.

## Shared parser preparation and invocation

`LanguageInstallService` supplies
[`SharedWpdaRuntimeFactory`](../../prattail/src/wpda_owned/backend.rs) to the
installed table. A table without a runtime factory refuses runtime installation;
it does not select the older recognizer as a fallback. Compile-time adapters
retain their generated typed-parser path.

The existing executable-image verifier produces a borrowed
`RuntimeParserAdmission`. Its private fields retain the exact immutable grammar,
image and admission limits. Direct factory callers must obtain the same receipt
through that verifier. The factory also checks its own compiler and Unicode
ABIs, then prepares owned descriptors through the original synthetic-rule,
classification, grouping and routing workers. All backends are prepared before
the installed-table batch is published. A preparation failure publishes none of
the earlier private backends.

`wpda_original_occurrences` is an explicit producer receipt in the canonical
grammar. The macro producer records original terms before appended collection
helpers; the DDL producer records its emitted original terms. Order and repeated
occurrences are preserved. An unavailable receipt is not an empty receipt and
is not recovered by filtering productions or reconstructing source.

An invocation borrows the existing capability-bound lexical session. Its
`AdmittedRuntimeGrammar` view lets declaration/action helpers reuse the checked
immutable Core without repeating whole-Core validation. Existing untrusted
helper constructors still validate; appended authored stores retain their own
validation and original provenance checks. These receipts establish data
admission, not installed-language authority.

Recognition and realization run the original weighted pushdown automaton (WPDA)
walker, graph-structured stack and shared packed parse forest. Per-invocation
limits check descriptor work and new forest nodes at their original work sites.
Result publication requires exhaustion of every accepting root's requested
family, no truncation among demanded nodes, and an aggregate result count within
the cap. Overflow or a semantic-action/key/resource failure is an error, never a
successful candidate prefix. Existing handle revalidation still precedes
publication, including after host callbacks.

The result's `ParseWeight` carries either the older exact cost/rank pair or the
complete original `LexicographicWeight`, without conversion or fabricated rank.
There is no cross-profile ordering. These parsing weights are distinct from
semantic cost grades and node funding/settlement.

A closed construction FLT is one reflected term, whereas the WPDA may report
several weighted derivations. The construction boundary inspects the complete
admitted family. If every reading has the same structural syntax, value and
hole-category telescope, it reflects that term once; differing readings fail
closed as ambiguous. It never elects the first reading by rank, turns the
family into Rholang parallel composition, or changes the parser's weighted
result. Receive-pattern preparation applies the same distinct-meaning refusal.
This is a publication rule for closed FLTs, not general parse pruning. Its
[closed-family proof](../../formal/rocq/prattail_wpda_runtime/theories/ClosedFltFamily.v)
states the exact-identity condition; semantic equivalence between distinct
trees requires separate checked evidence.

Guest-language variables and FLT template holes have different admission
rules. `admits_variables` gates the grammar's native variable production. A
typed FLT hole is supplied as a structural lattice edge by the host, not
lexed from guest text. Its ID, category and endpoint must be checked, and an
unknown or mismatched category is refused. A construction fill is then checked
against the installed category before publication. This lets a theory use
closed literal syntax while still allowing typed construction and receive
holes; it does not grant parser, construction or matching authority.

Scoped interface laws are checked in
[`InstalledRuntimeBackend`](../../formal/rocq/runtime_grammar/theories/InstalledRuntimeBackend.v),
[`InstalledWalkerResources`](../../formal/rocq/prattail_wpda_runtime/theories/InstalledWalkerResources.v)
and [`OwnedBackendPreparation`](../../formal/rocq/prattail_wpda_runtime/theories/OwnedBackendPreparation.v).
They cover admission ordering, unchanged inputs/weights, cumulative logical
capacity and success-only publication. They do not prove the complete parser
algorithm, universal grammar equivalence, physical memory bounds or public-node
execution. Source correspondence and actual consumer tests remain necessary.

## Cache rejection is not installation rejection

Parser and semantic images are replaceable caches. An invalid unsigned cache
may be discarded and regenerated from authoritative canonical input. The new
image must independently pass admission before publication. Consequently:

- A rejected cached artifact is never installed merely because it was cached.
- A valid replacement can allow installation to succeed.
- A compilation or final-admission failure leaves the published state unchanged.

The cache path is implemented by
[PreparedRegistryExecutableLanguage::install](../../mettail-elab/src/registry.rs).
It does not substitute a different source definition, grant rights, or provide
a legacy-parser fallback.

Image versions and compiler/Unicode versions are application binary interface
(ABI) commitments. At final admission, stale parser framing, parser compiler,
Unicode, semantic-image, semantic-compiler, and primitive-substrate ABIs are
rejected explicitly. An alias, fingerprint, reflected tag or registry URI
cannot substitute for an installed-language handle. Each operation rechecks its
required right and the handle's live generation; successful installation does
not make later revocation irrelevant.

## Acceptance correspondence

The [installation tests](../../rholang-runtime/src/language_install.rs) exercise
these boundaries directly:

| Obligation | Regression |
|---|---|
| Real inline Regex syntax and both executable images | `regex_gslt_module_compiles_and_installs_both_runtime_images_atomically` |
| Installed dispatch preserves original weighted Regex families, typed holes and explicit exhaustion | `practical_regex_ddl_drives_original_wpda_with_complete_owned_metadata` |
| Surface/value agreement | `greg_surface_and_canonical_value_lower_to_the_exact_same_language_core` |
| Equal grammar, distinct full theories | `identical_grammar_with_distinct_theories_installs_distinct_full_language_handles` |
| Action rights cannot amplify the manifest | `theory_actions_cannot_amplify_the_installation_manifest` |
| Late invalid artifact or ABI publishes no prefix | `parser_and_semantic_artifacts_are_admitted_before_atomic_publication` |
| Semantic-action budget preserves both tables and existing handles | `semantic_artifact_budget_rejection_preserves_both_installation_tables` |
| Language-count limit preserves both tables and existing handles | `installed_language_limit_rejection_preserves_both_installation_tables` |
| Invalid unsigned cache is recompiled and checked | `registry_module_recompiles_an_invalid_selected_unsigned_cache` |
| Staged programs release only after commit | `module_programs_stage_in_source_order_and_release_only_after_commit` |
| Revocation invalidates runtime tokens | `capability_tokens_are_reused_then_invalidated_across_revocation` |

The existing
[InstalledLanguageAuthority model](../../formal/rocq/runtime_grammar/theories/InstalledLanguageAuthority.v)
proves projection noninterference, requested-right checks, distinct modeled
full identities, no published prefix on artifact rejection, binding of both
artifacts, and revocation properties. Its identity representation is not a
proof that a concrete cryptographic hash has no collisions. Its abstract
artifact predicates require correspondence to the actual Rust verifiers.

Supporting models cover
[capability separation](../../formal/rocq/runtime_grammar/theories/CapabilitySeparation.v),
[language projection](../../formal/rocq/runtime_grammar/theories/LanguageCoreProjection.v),
[registry closure](../../formal/rocq/runtime_grammar/theories/RegistryModuleClosure.v),
[wire admission](../../formal/rocq/runtime_grammar/theories/WireAdmission.v),
[module staging](../../formal/rocq/runtime_grammar/theories/ModuleProgramStaging.v),
and [image admission](../../formal/rocq/runtime_grammar/theories/ImageAdmission.v).
These seven modules have been compiled and separately kernel-checked. They do
not constitute an extracted verification of the Rust service, exact
installed-count arithmetic, global parser completeness, or the complete node.
The tests and source review supply additional, explicitly bounded evidence.

## Dependency and execution checks

The node dependency is the exact revision in
[the checkout pin](../../.github/f1r3node-revision), using the isolated
`f1r3node-rust-f1r3lang` worktree named in `Cargo.toml`. The reviewed adapter
revision and its approved engine baseline are different identities: the
engine baseline remains recorded by the node's frontend admission contract.
The [checkout helper](../../scripts/ci/checkout-f1r3node-sibling.sh) requires an
exact match and refuses to move an existing mismatched checkout.

An existing-worktree check is not proof that the revision can be fetched from
the configured remote. Remote availability must be qualified before an
externally reproducible runnable revision is published. A local repository
override can test checkout mechanics but does not establish remote publication.

Run one heavy check at a time, retain artifacts under `target/`, and keep the
resource caps in place:

```sh
mkdir -p target/test-tmp target/verification
systemd-run --user --scope \
  -p MemoryMax=1G -p MemoryHigh=900M -p MemorySwapMax=0 -p TasksMax=32 \
  bash scripts/ci/checkout-f1r3node-sibling.sh
systemd-run --user --scope \
  -p MemoryMax=8G -p MemoryHigh=7680M -p MemorySwapMax=0 -p TasksMax=200 \
  env CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 TMPDIR="$PWD/target/test-tmp" \
  cargo test --locked --offline -p rholang-runtime --no-default-features \
    --features rholang-runtime --lib language_install::tests -- --test-threads=1
```

The focused installation suite passes all 69 tests, including the six stale-ABI
cases and the empty/pre-existing-state budget checks. The exact existing
dependency check passes. Fresh-checkout qualification is still open: local
fetch probes hit a Git thread-creation resource failure under the documented
cap. That failure is not evidence of repository corruption or a successful
remote checkout. Broad strict-lint closure remains a separate open gate; the
passing tests and model checks do not imply a clean workspace-wide Clippy run.

Installation acceptance is not the runnable Regex demonstration. That requires
the shared node language services, the MeTTaIL application entrypoint, and FLT
reduce/observe operations using the existing semantic kernel. A passing library
fixture cannot substitute for that node execution or its release checks.
