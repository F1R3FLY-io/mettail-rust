# Staged language capabilities in offered attempts

## Status and boundary

This is the **proposed ownership contract** for the OSLF/Cost(G) integration,
not a claim that offered production or validator replay already installs
MeTTaIL languages. The checked finite model is
[`StagedLanguageCapabilities.tla`](../../formal/tla/rho_bridge/StagedLanguageCapabilities.tla).
The pre-existing [installation lifecycle model](../../formal/tla/runtime_grammar/InstallLifecycle.tla)
checks one installed-table generation and atomic preparation; this model adds
two independent offered attempts, private-root reset, process-local capability
directories, immutable cache sharing, and replay reconstruction.

An *attempt* is a candidate evaluation or its independent validator replay.
A *private root* is the RSpace checkpoint from which that evaluation starts.
A *capability directory* maps an opaque Rholang private-name byte string to a
sealed installed handle; the byte string alone is not authorization. An
*artifact cache* holds compiled immutable parser/semantic data, not handles,
revocation authorities, or live generation counters. A *generation* is the
per-language revocation epoch within one directory. The model's *incarnation*
counts reset/retry lifetimes; it is a ghost identifier, **not** a field already
present in Rholang capability bytes.

## Source-backed ownership choice

Use a **fresh attempt-owned installer and directory** for each offered
candidate and a different fresh one for independent replay. In concrete
terms, the attempt must own the whole `RholangLanguageRuntime` together with
its `LanguageInstallService`, `InstalledLanguageTable`, revocation map, and
`CapabilityState`; creating only a fresh `RholangLanguageRuntime` around a
shared `LanguageInstallService` would still share mutable authority.
Immutable registry snapshots and admitted compiled artifacts may be shared by
reference after their existing verification. The factory must be called after
the authenticated root, envelope, adopted policy and frontend are fixed, but
before any language system definition is installed into the private runtime.

The current [Rholang-facing implementation](../../rholang-runtime/src/language_install.rs)
already separates the injected registry snapshot from the installed table and
revocation map (`LanguageInstallService`), keeps token generations, entries,
prepared patterns and admissions in `CapabilityState`, checks the sealed table
again on `resolve`, and invalidates entries/patterns/admissions on `revoke`.
`install_all` acquires the capability-directory lock around the service's
atomic batch commit. `language_runtime_definitions_with_theorem_checker`
constructs install, parse, FLT, theorem and semantic handlers from the same
runtime instance. These are useful local building blocks; **they do not yet
establish attempt ownership** in the node.

The [native offered producer](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/execution.rs)
spawns a private runtime, resets it to `prepared.execution_root`, and reverts
its soft checkpoint on evaluation failures. Its `NativeOfferedAttempt::abort`
resets RSpace to that root. The
[node runtime manager](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/runtime_manager.rs)
has a distinct `spawn_offered_runtime`; the
[independent witness replay](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/execution/replay.rs)
builds a separate replay environment and later a fresh offered runtime. Those
paths currently install the native offered/grant definitions, not a proved
attempt-scoped MeTTaIL capability factory. The integration seam is to inject
the same attempt-local language-definition bundle at both runtime creation
sites, with no new Rholang public ABI, registry policy, price/limit change, or
consensus activation.

The intended transition order is:

```text
authenticated root + signed terms + pinned registry + host policy
  -> fresh attempt-local service/table/directory
  -> stage every admitted artifact (shared immutable cache allowed)
  -> atomically install the complete batch in the private directory
  -> execute and validate Cost(G)/OSLF obligations on that attempt
  -> publish only after native funding, evidence and replay checks succeed
  -> on failure, abort/reset and destroy attempt-local authority

validator replay: same authenticated inputs -> a *new* directory -> same
checked semantic observation and native settlement, never borrowed play state
```

The model deliberately leaves the existing native `OslfResourceLogic<RhoGslt>`
funding gate, monetary case, `Phlo` price/limit, ledger and atomic RSpace
settlement outside its state. It specifies the ownership prerequisite for
feeding checked guest demand to that gate, not an alternative gate or ledger.

## Finite model and checks

The model is quantified over its finite language set. The primary bounded
configuration has two attempts, two roots, one language, two retry
incarnations and two revocation generations. A separate
[`TwoLanguageSafety.cfg`](../../formal/tla/rho_bridge/StagedLanguageCapabilitiesTwoLanguageSafety.cfg)
uses two languages with one incarnation and generation to check that
revocation and staging of one language leave the other live. `Stage` can warm the shared
canonical cache but does not issue authority. `Commit` publishes the complete
staged set in one transition; `Reject` discards it. `Revoke` removes the live
token and advances only its language generation. `Abort` and `Reset` clear the
local directory, issued-token provenance, staged work and private observations;
the global immutable cache may remain. `Begin` can then retry with a fresh
incarnation. `Observe` represents a deterministic, authenticated semantic
result keyed by root and language. It abstracts the actual parser, rule
evaluation, funding projection and native replay algorithm.

The abstract `Token` is language plus generation, with **no attempt component**.
This reflects the important limitation of today's `capability_token_id`: its
hash includes language fingerprint, generation, rights and install-policy
fingerprint, but no private-root or attempt nonce. Equal bytes can therefore
be minted independently in two fresh directories. The model proves that one
directory's bytes grant nothing in a sibling **unless that sibling has its own
live sealed entry**. It does not prove global byte uniqueness or that a leaked
old token cannot alias an independently minted equal token after a fresh
retry. If such bytes can survive an aborted private root, the implementation
must either rule out that escape at the publication boundary or add a
deterministic, replay-reconstructible namespace to the private authority
identity. Random non-replayable salts would violate replay identity.

| Checked invariant | Meaning | Concrete property / implementation boundary |
|---|---|---|
| `SiblingLocalStateStable` | Every action by one attempt preserves the other's root, phase, stage, table, generations and observations | Interleave two `NativeOfferedAttempt`s from equal and unequal roots; abort/revoke one; assert the other's handles and observations are unchanged. Factory owns separate service/table/directory instances. |
| `StageAndRejectDoNotPublish`, `LiveWasLocallyIssued` | Cached or rejected preparation cannot create an authorized token; only local complete commit can issue one | Late-invalid export and host-budget failures preserve both the installed table and capability directory; cached artifact alone never resolves. Extend existing `install_all` atomic-batch tests to the attempt factory. |
| `InactiveHasNoAuthority` | Abort/reset removes all local authority, staged work and private observations | Install, evaluate, abort, reset, retry; old directory is inaccessible and no failed output or authority is published to the parent root. Test cancellation and late `spawn_blocking` completion too: a late install must not resurrect a closed attempt. |
| `LiveUsesCurrentGeneration`, `OtherLanguageUnaffectedByRevoke` | Revoke makes the old token unusable and preserves another language's live token and generation; reinstall issues only the advanced generation | Extend `capability_tokens_are_reused_then_invalidated_across_revocation` with two languages and with offered play/replay attempts; old token/pattern refused, other language remains live. |
| `ObservationsAreRooted`, `IndependentReplayAgrees` | Independent replay of the same authenticated root and language observes the same abstract result | Recreate installation and a checked guest step in a fresh replay service; compare exact semantic receipts and native event/cost evidence. Change root, registry commitment or signed policy and require refusal. |
| `CanonicalCacheContents`, `CacheOnlyGrows` | Cache entries remain canonical immutable data and cannot substitute for mutable authority | Share verified artifact `Arc`s across two factories, then revoke/abort one; the other continues, while the aborted one cannot resolve from cache alone. |

The safe [`Safety.cfg`](../../formal/tla/rho_bridge/StagedLanguageCapabilitiesSafety.cfg)
and two-language configuration check all listed invariants. Seven negative controls deliberately inject
cross-attempt sharing, abort leakage, reset leakage, stale-generation revival,
replay drift, cache-derived authority and collateral revocation. Each has its own `.cfg` and must fail
its named invariant; an expected counterexample is validation that the
property is live, not a success of the unsafe design. The model is a finite
state check of an abstract transition system, not a proof of Rust refinement,
cryptographic collision resistance, scheduler fairness, cancellation safety,
all Rholang evaluation, or monetary settlement.

On 2026-10-10, both positive configurations passed all listed invariants,
including `OtherLanguageUnaffectedByRevoke`. The primary configuration explored
82,613 distinct states. The two-language configuration explored 1,820,673
distinct states. Both exhausted their queues without an invariant error.
All seven unsafe configurations produced the intended invariant violation:
`SiblingLocalStateStable`, `InactiveHasNoAuthority` (abort and reset),
`LiveUsesCurrentGeneration`, `ObservationsAreRooted`, `LiveWasLocallyIssued`,
and `OtherLanguageUnaffectedByRevoke`. Complete logs are in `target/verification`.
These completed configurations are finite samples, not a mathematical proof
of arbitrary populations.

The focused checker commands use one TLC worker and a bounded Java heap, and
must run serially under the campaign's resource lane:

```sh
mkdir -p ../../../target/formal ../../../target/verification
systemd-run --user --scope -p MemoryMax=512M -p MemorySwapMax=0 \
  -p CPUQuota=100% env JAVA_TOOL_OPTIONS=-Xmx384m \
  tlc -cleanup -workers 1 -metadir ../../../target/formal \
  -config StagedLanguageCapabilitiesSafety.cfg \
  StagedLanguageCapabilities.tla \
  > ../../../target/verification/staged-language-safety.log 2>&1
```

Run from `formal/tla/rho_bridge`. The seven `*Unsafe.cfg` files use the same
command shape; require a nonzero TLC exit and the expected invariant-violation
line for each. Preserve logs under `target/verification`, not a false green
summary. Model results and any counterexamples must be reported separately
from the still-pending Rust property/refinement tests.

## Remaining refinement obligations

1. Bind the attempt factory to the **actual** producer, replay, abort and reset
   lifetimes. A stale `Arc` retained by a handler or late blocking task must
   not commit after the attempt is closed. The finite model treats each
   transition as atomic and does not prove this concurrency property.
2. Pin the same registry snapshot, canonical images, host grant policy and
   authenticated private root in play and replay; reject mismatches before
   checked demand or native funding publication. Neither text nor a cached
   artifact becomes authority.
3. Prove byte-level stale-token safety at the cross-attempt publication
   boundary. Within one directory, generation revocation is modeled and
   already implemented; fresh-directory token-byte aliasing is not silently
   treated as impossible.
4. Connect the checked complete guest candidate roster and its Cost(G)
   receipts to the existing native offered funding provider, then compare
   independent replay's exact receipts and settlement. This model does not
   discharge the separate Cost(G)-to-demand conservativity/equality proof or
   any consensus activation criterion.
