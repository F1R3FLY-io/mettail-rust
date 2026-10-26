# Cost(G) funding at an authenticated native prefix

Status: source-backed contract and small mathematical refinement model. This
document does not activate a protocol or implement a live supply adapter.
The structural-demand-to-physical-authority correspondence below remains an
explicit proof and implementation obligation.

This supplements [Funding Projection V2](cost-g-funding-projection-v2.md).
It preserves the complete enabled-candidate roster, the client's signed
`phlo_price` and `phlo_limit`, and one native monetary funding case.

## 1. Result: two checks, not a conversion rate

Cost(G), the cost-accounted extension of a guest grammar G, grades a forced
interaction by its consumed signature. OSLF (Operational Semantics in Logical
Form) supplies the logic for that graded transition system. Its token-sufficiency
judgment is not a byte measurement or a currency amount.

The papers distinguish the signature guard, authority to approach a located
stack, and sufficiency of tokens. The native implementation also checks
class-weighted execution resources and monetary acquisition. Neither paper
defines a conversion from measured bytes to guest grades. The required
composition retains both obligations; it does not equate their numbers.

The sources are the companion paper's **Graded adequacy**, **Capabilities**, and
**Resource sufficiency** sections [P2], and the rho paper's **Static Analysis as a
Linear Resource Proof** and **Data-Dependent Interaction** sections [P1].

| Quantity | Actual unit and source | Not interchangeable with |
|---|---|---|
| Guest Cost(G) grade | Signature-monoid grade of a forced transition [P2] | Host currency or semantic-search work |
| Paper token demand | Signed-layer/token obligations, indexed by signature [P1] | Encoded term bytes |
| Native structural bound | Conservative potential send/receive introductions under signed scopes; empty signed layers and stack-transfer obligations also contribute [H1] | Measured successful COMM count |
| Physical authority presentation | Signature atoms and stack cells checked against the supplied event sequence; native chronology requires the refinement in section 4 [H2] | An unauthenticated lane map |
| Native measurements | Interaction count, introduction bytes, transfer bytes, trace bytes [H3] | A single homogeneous token quantity |
| Native resource quantity | Quantity at an exact location, class, acquisition terms, and authority [H4] | Signature identity alone |
| Weighted phlo usage | Resource quantity multiplied by class weight and authority multiplicity [H4] | REV amount or structural demand |
| Acquisition charge | Fresh weighted usage times the signed actual price, plus the prescribed fee [H4] | A new guest charge or new price policy |

The analyzer's syntax-specific bound is not asserted equal to the paper's
signed-node recurrence. The paper writes one plus the body demand at every
matching signed layer. The current analyzer tracks introductions under native
wrapping and treats a signed body without an introduction separately. A
soundness correspondence must account for that distinction [H1]. The paper's
older unknown-plus-margin sketch is not sufficient evidence: the current host
rejects an unprovable structural demand [H5].

## 2. Existing authority is the only authority

The canonical lane is `cost_signature_to_sig(signature).lane_hash()`. A deploy's
outer signer is not an alias for an inner signature. A compound signature is
not permission to spend just one of its constituents. Existing native event
verification and signature-atom comparison decide admissible split/join
presentations. A hash or guest grade alone proves neither possession nor the
right to draw from a purse [H1, H2, H6].

The authenticated inventory retains more than lanes:

- A rooted wallet source has a custody identity and an authenticated payer.
  Multiple lanes that share custody consume one capacity. The physical checker
  sums their debit before it subtracts from the remaining custody balance.
- A captured stack has its rooted identity, cell order, and branch tree.
  Children become available only after their ancestor gates were met by prior
  events. A parent popped during the same event does not release its child.
- A stack born during execution is unavailable through its last required
  transfer event. Its cells become eligible only at a later event.
- A prepaid economic resource retains its location, class, acquisition terms,
  authority, origin, and contributing sources. Signed source permissions match
  the complete resource wire key. Private-name on-chain authority needs the
  existing independently observed native evidence [H2, H6, H7, H8].

The native physical checker presently inserts a rooted wallet source's
`capacity` into the physical custody inventory. This is a fact about that
checker's input, not proof that a REV balance is an interchangeable token count.
Its result remains subject to the independent measured economic check [H6].

## 3. The relational supply contract

Let $`r`$ be the authenticated pre-state root and $`p`$ an authenticated native
operation prefix. Its event projection must preserve the established causal
dependencies. A numeric event boundary requires a checked ordered projection,
not an arbitrary vector position. This contract does not impose a total order
on unrelated concurrent operations. Let $`W`$ be a host-owned witness that retains the
rooted inventory, exact authority presentations, custody allocation, stack
positions, birth availability, and applicable rights at that prefix. Let
$`S(s)`$ denote an abstract signature-token capacity for lane $`s`$.

Write $`A(r,p,W,S)`$ for the checked relation that this witness realizes this
abstract capacity at that prefix. The accompanying model now instantiates this
relation as `concrete_authenticated_prefix`, using the existing native models
listed in section 6. It is not an implemented Rust constructor or an additional
ledger. Extracting its inputs from the checked native inventory remains a
Rust-refinement obligation. Projecting all current wallet balances to lane
counts does not establish this relation.

For a complete, nonempty roster of enabled candidate occurrences $`C`$, let
$`D_c(s)`$ be the bound authenticated by `OslfResourceLogic` for the canonical
host demand of occurrence $`c`$. Preserve occurrence multiplicity and owner
identity. The approved shared-supply obligation is:

```math
\exists W,S.\quad A(r,p,W,S)\ \land\
  \forall c\in C,\ \forall s,\ D_c(s)\leq S(s).
```

The same witness and supply cover every alternative. The candidates are not
all executed and are not all charged. Native execution still has one measured
monetary case. A candidate check must not mutate or spend the witness while
examining an alternative.

For finite $`C`$, define the pointwise envelope $`E(s)=\max_{c\in C}D_c(s)`$.
The displayed obligation is equivalent to the existence of a feasible witness
whose supply covers $`E`$. This is a logical characterization, not a claim that
the envelope is itself physically realizable or that a rectangular lane map
captures temporal availability.

For example, one custody of capacity one may separately fund vectors
$`(1,0)`$ and $`(0,1)`$. It cannot fund one common supply dominating both.
Replacing the displayed quantifier order with “for each candidate there exists
some separately feasible supply” would weaken the approved V2 condition.

The measured monetary obligation remains separate:

```math
\exists M.\quad
  \mathrm{NativeEconomicCheck}(r,\text{signed controls},\text{measured trace},M).
```

The economic witness $`M`$ retains full resource keys and source eligibility.
The two witnesses must belong to the same staged attempt, root, and native
trace; sharing an arbitrary numeric total is not that binding. Reuse
`check_funding_assignment`, `select_phlo_funding_family`, and their existing
capacity and eligibility constraints where allocation is needed [H8, H9].
Do not implement a second flow solver or reserve a second monetary case.

There is a second reason to retain the witness. Numeric dominance is not a
license to weaken a compound physical cell. A cell containing both signatures
$`a`$ and $`b`$ has enough atom counts to dominate $`a`$, but native admission
requires exact coverage of the complete presentation. It does not permit a
partial draw of that cell. The model retains this exact-cover judgment beside
the numerical projection. It does not assert downward closure of physical
drawability. The actual transition/presentation correspondence must remain
checked, even when the conservative numerical funding check succeeds.

## 4. Native chronology and the missing correspondence

The native path evaluates privately, records authority and byte observations,
checks rooted settlement, and permits publication only after the existing
verification/replay boundary. Supply is not an authenticated preprocessing
callback. A language installed while Rholang evaluates must attach its guest
obligation to the current staged native attempt and guarded operation position.
The installation's grade image and host projection do not own wallet authority.

`CheckedPrepaidPhysicalTrace` borrows the supplied authority-event vector.
`verify_physical_settlement` checks event/draw identity,
signature presentations, shared custody, and stack readiness against that
vector's positions [H2, H6]. This does not authenticate the vector's chronology.
`AuthorityRuntimeState.events` is a `BTreeMap` keyed by event identity.
`RuntimeBudget::authority_events` emits that map's key order [H10]. The producer
passes this vector to `checked_physical_trace` [H7]. Hash-key order alone does
not establish execution order or an operation prefix.

The existing operation evidence retains session, causal path, predecessors,
observation links, and budget intervals [H11]. The adapter must establish the
authority-event projection from that evidence. It must not infer chronology
from an event hash or sort unrelated operations into an invented dependency.
If the verifier needs a linear sequence, its selected order requires explicit
authentication and must respect the relevant causal dependencies. No equivalence
between arbitrary linearizations is asserted here.

In the inspected producer,
`checked_physical_trace` is invoked on the branched-stack path; the ordinary
path uses `select_measured_demand`. This document does not assert that every
ordinary path already exposes a checked prefix witness [H7].

The missing theorem is a refinement theorem, not a price choice:

> For an accepted installed projection, a complete authenticated grade roster,
> and the original rooted native attempt prefix, the verified structural host
> demand conservatively accounts for the authority presentations required by
> each corresponding guest transition. A native witness realizes the claimed
> abstract supply only when the relevant presentations are jointly admissible
> under the existing custody, located-authority, compound-signature, transfer,
> birth, and prior-event stack rules. The evidence refers to that same prefix
> during producer checking and independent replay.

Numeric dominance alone is not this theorem. A sufficient token count can be
unusable at the required time or location. A conservative upper bound proves
sufficiency when supplied; it does not manufacture an exact transition or
post-state. Supply below an upper bound also does not prove that the actual
execution is underfunded.

To discharge the theorem, the prefix adapter must connect these existing seams:

1. Bind the complete roster to installed base/cost/projection identities and the
   original operation position before reducing it to observable results.
2. Verify the canonical `Par` bound through the existing resource-logic verifier.
   Retain whether evidence is exact or only conservative.
3. Obtain the prefix witness from the existing rooted physical-authority
   machinery, including non-branched paths. Establish the structural-demand
   correspondence above. Parsed stack syntax and future events are not supply.
4. Retain the obligation in the attempt's checked evidence. Producer and replay
   must check the same complete roster and prefix before publication.
5. Preserve measured native settlement, source permissions, and signed
   price/limit. Guest proof/search work remains separately bounded. Do not
   create fake byte observations to represent guest demand.

These are obligations for the tracked prefix-view, obligation-record/order,
roster-ingress, producer-gate, and replay-gate leaves. They are not production
changes made by this document.

### 4.1 Planned extraction from the existing verifier

The minimal prefix view retains state from the existing physical verification
traversal. It does not rerun allocation or apply settlement. The verifier already
maintains custody remainders, stack positions, complete branch lanes, and birth
availability [H2]. Its returned settlement does not expose that intermediate
state. `VerifiedPurseStackPops` retains cumulative pops and branch roots, which
are insufficient to recover chronology or custody remainders [H14].

For an authenticated ordered projection, let $`k`$ count the verified events
strictly before the guarded boundary. The planned read-only view must retain:

- The original inventory, signatures, complete event projection, and verified draws.
- Boundary $`k`$, remaining physical custody balances, and exact per-branch stack positions.
- Original root identities, whole compound cells, and complete ancestor gates.
- Complete root-level birth metadata, including transfer identities after the boundary.

Only the prior draws contribute to the remainder and stack positions. The
view must retain their connection to the complete checked trace. It must not
publish a partial result when verification refuses.

`born_stack_availability` checks every born root against all required transfer
events [H2]. It counts cells across the root's complete branch tree. A selected
root becomes available only after its latest required transfer. Slicing the
event vector before this lookup removes future transfer identities and can
reject an otherwise valid earlier prefix. Removing future birth records instead
would discard authoritative validation. Retain the complete lookup and apply
the strict-before-boundary check when selecting a source.

The current `checked_physical_trace` constructor fills wallet lanes and captured
pre-state stacks. It does not populate `AuthorityPhysicalInventory::born_stacks`
[H6]. `derive_live_born_stacks` authenticates observed births against rooted
post-state stacks elsewhere [H7]. These paths are not already connected by a
prefix-view interface. A view over the current capture cannot claim newly born
supply without that explicit refinement.

### 4.2 Bindings that extraction alone cannot establish

The outer adapter must retain `DirectWalletPolicySnapshot` and
`NativePrepaidInventory` from the same authenticated original root [H6, H12].
Root equality does not establish envelope, terms, controls, or operation identity.
`NativeOfferedAttempt::bind_policy` already checks root, envelope identity,
schedule commitment, actual price, and signed limit [H13]. Reuse that binding
and authenticate the guarded operation occurrence separately. A caller-supplied
prefix number or the live settlement root cannot replace the original binding.

The physical verifier checks signature atoms and selected stack identities.
It does not establish the model's `prefix_near` predicate [H2, F3].
`PurseStack` retains channel and source identity. Prepaid resources retain
location, class, acquisition terms, and authority [H4, H6, H14]. Those fields
preserve resource identity but do not independently authenticate the guarded
operation's access to each source. This operation-to-source accessibility
mapping remains explicit. Neither signature equality nor an unconditional
predicate may replace it.

The required refinement must connect verifier state at $`k`$ to the model's
folded custody debit, exact stack suffixes, birth readiness, and complete
ancestor gates. It must also authenticate the event projection and located
requests under the same attempt, root, signed controls, and operation prefix.
These are source-refinement obligations, not additional allocation policies.

A prefix view alone is not `NativePresentationChecked`. The presentation check
must preserve whole cells and shared custody while establishing one witness for
the complete roster. It must not allocate independently for each candidate,
sum alternative candidates, manufacture an executed authority event, or create
a monetary funding case.

## 5. Supplying artifacts does not grant spending authority

Providing a language, projection, token representation, or supply assertion
does not grant the authority to spend a physical source. The papers separate
the matching key from authority to approach a located purse [P2]. The existing
host source permissions, payer authentication, and on-chain authority evidence
remain controlling [H6, H8].

`grammar-core::LanguageRight` includes `Spend` [M1]. A language-level `Spend`
request is not a wallet signature or a funding-source permission. Each native
draw still requires authenticated source permissions, the exact signature
presentation, and the applicable located-access check.

The paper derives located access from matching interaction surfaces through
`near`. It does not define a `Provision` API or require a new language right
[P2]. This contract adds no such requirement. In the small model,
`source_may_provision` distinguishes supplying a source from permission to spend
it. The checker never accepts that Boolean as spending authority.

## 6. What the accompanying proof does and does not establish

[NativePrefixSupply.v](../../formal/rocq/rho_bridge/theories/NativePrefixSupply.v)
reuses `is_funded` and `law_sound` from `MettaFundingLawsConformance.v`. It also
imports the existing native funding and stack models directly [F1–F5].

It proves the least pointwise envelope law, common-witness equivalence, and the
conditional composition with the existing lane check. The generic relation is
then instantiated with `NativePrefixChecked` and `NativePresentationChecked`.
These records collect concrete checks; they do not assume the desired
conservation or projection theorem as a field.

| Model check | Reused definition or theorem | Derived result |
|---|---|---|
| Root, envelope, signed controls | `capture_native_snapshot`, `native_execution_binding_exact` [F1] | Root and original controls are retained |
| Wallet owners | `direct_wallet_authorization_exact` [F4] | Each selected custody has an authorized owner and captured rooted balance |
| Prior and current wallet draws | `physically_admissible`, `physical_draw`, `settled_balance` [F4] | Their combined debit fits one custody capacity and conserves that balance |
| Located stack admission | `request_admitted`, `located_history` [F3] | Selected stacks are near the interaction surface, and ordered residuals are exact |
| Full compound presentation | `exact_cover_preserves_each_atom` [F2] | Every authority atom and its multiplicity are preserved, without partial-cell weakening |
| Birth chronology | `causal_stack_history`, `birth_ready_at` [F5] | Every required birth event strictly precedes selected use |
| Shared-prefix ancestry | Explicit ancestor list and count of prior selections | Each ancestor gate is met by prior events, never a same-event pop |

The prefix data include the original ordered event projection: each entry
contains a stack request and its wallet draw. The current wallet remainder is
derived by folding the prior draws and applying the existing `settled_balance`.
It is not a separately mutable balance. Stack residuals come from the existing
located and causal history predicates. Birth metadata is checked against the
root-level birth inventory; child lanes inherit the birth-event set of their
root. This keeps a root's complete transfer set distinct from a child's cell
count.

`concrete_roster_instantiates_relational_funding` supplies the original common
witness relation. `concrete_roster_retains_joint_backing` derives the custody
bound, full compound atom equality, and the existing per-lane funding result
together. A complete finite rooted input and compound presentation instantiate
this relation, and a one-candidate roster passes the existing lane predicate.
A companion closed example rejects drawing only one constituent of that same
compound cell.

A separate composition lemma retains both physical and monetary witnesses
without requiring equal numeric budgets.
`same_invocation_two_axis_composition` indexes both predicates by one complete
invocation identity. Its root, prefix, session, generation, operation, and
ordinal are shared. The runtime must authenticate those indexed predicates.
The lemma does not authenticate arbitrary untrusted records.

`staged_common_supply_iff_concrete_prefix` instantiates the staged journal's
common-witness contract with a native presentation and its lane supply.
It proves equivalence to the relational roster check, with explicit root and
prefix equality. This closes the model-level connection to
[staged publication](staged-guest-funding-obligations.md). Each candidate still
needs its checked bound. The native interpretation must still establish the
demand-to-presentation correspondence.

`conservative_analyzer_composes_with_relational_supply` states analyzer
soundness as an explicit hypothesis and proves only its composition with a
supplied relational witness. The finite one-lane example independently specifies
an actual demand of one and a conservative bound of two; it is not a proof of
the Rholang analyzer.

Closed finite examples and local gate laws establish:

- Equal authority lanes do not imply equal resource class, terms, or location.
- Two individually feasible alternatives need not have a common feasible supply.
- Shared custody cannot be counted as two independent balances.
- A funded outer-signature lane cannot cover an unfunded inner-signature lane.
- Exact-key eligibility retains root, Spend, and full resource identity.
- A future or same-event birth cannot supply an earlier event.
- Permission to supply a source, without Spend, cannot authorize a draw.
- A same-event parent pop cannot satisfy a previously unmet child gate, while a
  prior-event pop satisfies that local gate.

The natural-number model abstracts cryptographic bytes, checked integer bounds,
and authenticated source construction. It is not a proof of hash injectivity,
signature authentication, the entire allocator, the Rholang analyzer, arbitrary
Rust stack traces, or Rust refinement. The rooted stack reader, canonical
signature decoder, root-to-branch mapping, ancestor lists, event projection, and
located permission predicate are explicit input data. The model checks their
stated relationships and consequences; it does not prove the not-yet-written
Rust adapter extracts those data correctly. In particular, the ancestry lemma
does not prove that an arbitrary supplied ancestor list is the native tree's
complete list. That list must come from the checked native tree enumeration,
not a guest claim. Exact presentation checks do not replace this provenance
obligation. Its full-key eligibility model describes the
economic side; it does not replace native compound-signature presentation rules.
Its provision/spend Booleans express the separation obligation. They do not
specify an additional language-right API.

Focused future executable checks must exercise the actual host implementations:
same-custody aliases, class/terms/location mismatch, private-name authority,
compound partial draws, future transfers, same-event branch release, ordinary
linear stacks, empty/incomplete rosters, and producer/replay prefix mismatch.
Use an independent finite allocation oracle, not the production selector as its
own expected result. Existing `funding_assignment` tests already compare an
independent wide-integer oracle; reuse that pattern [H9]. All ordinary native
behavior and full host closure remain required.

Validation: the concrete native-import model and staged composition passed
`coqc` and independent `coqchk -silent` on 2026-10-10. Both exited zero, with
27 closed assumption reports. The serialized gate used:

```sh
systemd-run --user --scope -q --expand-environment=no \
  -p MemoryMax=512M -p MemorySwapMax=0 -p CPUQuota=100% -p TasksMax=32 \
  coqc -Q target/formal/oslf-alignment-20261010 CostAccountedRho \
  -Q target/formal/native-prefix-supply-concrete-20261010 RhoBridge \
  target/formal/native-prefix-supply-concrete-20261010/NativePrefixSupply.v
```

The command is shown relative to the repository root; the executed gate used
absolute paths. The kernel check used the same two load paths and checked
`RhoBridge.NativePrefixSupply`. The gate used the native transitive dependency
closure and bridge sources under `target/formal`. Source copies matched before
compiled dependencies were reused. It compiled the changed models, not the
entire native formal suite.

The current passing log is
`target/verification/native-prefix-staged-composition-20261010.log`.
The gate reused source-matched native proof dependencies, including the updated
staged journal model. No admitted statement or new axiom was introduced.

The standard bridge Makefile now supplies the `CostAccountedRho` load path and
focused native dependencies in addition to the `_CoqProject` registration.
`NATIVE_COST_ACCOUNTED_RHO` selects the native `formal/rocq/cost_accounted_rho`
directory; its default follows the root Cargo workspace's native checkout path.
The Makefile snapshots only the dependency closure under
`target/formal/rho_bridge-native/<native-root-hash>`. Source timestamps refresh
the snapshots; changing the native root selects a different cache. Regeneration
invalidates the generated dependency index, which is rebuilt automatically.
The bridge delegates requested targets to the generated Makefile only after
generation, so a previously included regeneration rule cannot discard the new
native load path.

Makefile generation and a dry-run of `theories/NativePrefixSupply.vo` passed,
including the native dependency commands and their load path. The log is
`target/verification/native-prefix-build-wiring-20261010-r4.log`. The standard
route was not compiled again while another lane ran Rust tests. This dry-run is
build-wiring evidence, not a replacement for the independent passing proof gate.
No Rust build was run in this lane. No live-integration completion is claimed.

### 6.1 Checked prefix extraction

[`NativePrefixCut.v`](../../formal/rocq/rho_bridge/theories/NativePrefixCut.v)
extends the same native histories without replacing their transition rules.
It splits a checked history at a bounded position and derives the exact stack
remainder. The complete birth lookup still refers to the original inventory.
The located-history split retains the original access predicate.

Both views have identical remaining cells when their initial inventory and
request projection agree. This follows from the existing native theorem for
admitted stack histories. It does not authenticate arbitrary input projections.

Birth readiness depends on which required transfer events precede the cut.
Changing positions without changing that membership preserves local readiness.
This is not a claim that arbitrary schedules preserve all physical state.
The closed counterexamples distinguish two important failures:

- Equal event sets do not establish equal ordered stack behavior.
- A truncated lookup can preserve local readiness but invalidate global birth metadata.

All twelve assumption reports are closed. Compilation and independent kernel
checking passed under a 512 MiB limit. The source and checked copy have the
same SHA-256 digest. The log is
`target/verification/native-prefix-cut-20261010.log`.
Normal Makefile generation and the focused target dry-run also passed.
That log is `target/verification/native-prefix-cut-build-wiring-20261010.log`.

The [integration verification ledger](oslf-integration-verification.md#prefix-order-is-an-input-obligation-not-a-hash-property)
maps each invariant to existing tests and remaining implementation obligations.
Five native prefix tests passed, including two 128-case property tests.
A separate private-session test failed on a Legacy codec epoch mismatch before
its readiness assertion. These results do not certify the missing runtime adapter.

## 7. Source ledger

Inspected on 2026-10-10 in the campaign worktrees. Host HEAD was
`e5102e945e21dd6e78e2ae73ef48ed71304238bc`; MeTTaIL HEAD was
`c94dce17ad5cb977cde1dfacb85b61d8a83d43c8`. Both worktrees contained concurrent
uncommitted changes. Symbol names below are authoritative over moving line
numbers.

- **[P1]** [cost-accounted-rho.tex](../../../../publications/cost-accounting/cost-accounted-rho.tex),
  token demand/supply and conservative envelope, lines 1994–2135; compound
  partial-consumption restriction, lines 1178–1205.
- **[P2]** [continued-gslt-cost-v2.tex](../../../../publications/cost-accounting-as-monad/continued-gslt-cost-v2.tex),
  graded adequacy, lines 837–865; capabilities, lines 1244–1396; token discipline
  and resource sufficiency, lines 1400–1536.
- **[H1]** [delta_sigma.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/delta_sigma.rs),
  `SigKey`, `DemandEntry`, `DemandTask::SignedFinish`, `DemandTask::Stack`,
  `demand_bound`, and `static_authority_plan`.
- **[H2]** [authority.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/authority.rs),
  `AuthorityPhysicalInventory`, `stack_lane_ready`, `born_stack_availability`,
  `physicalize_balance_debit`, `verify_physical_settlement`.
- **[H3]** [measurements.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_phlo_rules/measurements.rs),
  `NativePhloMeasurement`, `NativePhloRules::measure`, and `occurrences`.
- **[H4]** [phlo_execution.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/phlo_execution.rs),
  `PhloResourceAmount`, full resource aggregation, `weighted_usage`,
  `check_execution_resources`; also
  [native execution policy](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_phlo_rules/execution.rs).
- **[H5]** [resource_logic.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/resource_logic.rs),
  `OslfResourceLogic::verify_demand_bound`, `is_funded_bound`,
  `resource_observation`, and `DefaultResourceLogic`.
- **[H6]** [inventory.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/prepaid_receipts/inventory.rs),
  `CheckedPrepaidPhysicalTrace`, `NativePrepaidInventory`, `NativePrepaidPrefix`,
  `checked_physical_trace`, and `prefixes_verified`.
- **[H7]** [producer.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/execution/producer.rs),
  branched physical-trace selection and measured-demand binding, lines 945–1014;
  `derive_live_born_stacks`, existing rooted native settlement, and signed-limit checks.
- **[H8]** [family_selection.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/execution/family_selection.rs),
  `select_rooted_native_family`, exact signed resource eligibility, the singleton
  `PhloFundingRequirement` array; and
  [prepaid cell validation](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/prepaid_receipts/cell.rs),
  `check_resource` and `check_contributions`.
- **[H9]** [funding_assignment.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/monetary_allocation/funding_assignment.rs),
  `check_funding_assignment`, source row bounds, exact obligation columns,
  eligibility and overflow checks, independent finite and property tests.
- **[H10]** [accounting/mod.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/mod.rs),
  `AuthorityRuntimeState::events` and `RuntimeBudget::authority_events`:
  event-identity map storage and key-ordered output.
- **[H11]** [operations.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_runtime/operations.rs),
  `NativeOperationOccurrence`, `NativeOperationRecord`, and
  `NativeOperationRecordV3`; also
  [checked_operations.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_runtime/checked_operations.rs),
  `CheckedNativeOperationJournal`, and
  [recording.rs](../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/native_runtime/recording.rs),
  `NativeBudgetRecording`.
- **[H12]** [policy_snapshot.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/policy_snapshot.rs),
  `DirectWalletPolicySnapshot`; and
  [snapshot.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/snapshot.rs),
  `DirectWalletSnapshot` and `DirectWalletFunding::read_snapshot`.
- **[H13]** [execution.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/direct_wallet_funding/execution.rs),
  `NativeOfferedAttempt::bind_policy`, original-root and signed-control checks.
- **[H14]** [supply.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/supply.rs),
  `PurseStack`, `VerifiedPurseStackPops`, and `verify_purse_stack_pops`; also
  [inventory/demand.rs](../../../../f1r3node-rust-f1r3lang/casper/src/rust/util/rholang/costacc/prepaid_receipts/inventory/demand.rs),
  `NativePrepaidDemandBinding` and `bind_measured_demand_with_prefixes`.
- **[M1]** [installed.rs](../../grammar-core/src/installed.rs),
  `LanguageRight`, `LanguageRights`, and installed funding-projection ownership.
- **[F1]** [NativeFundingSnapshot.v](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/NativeFundingSnapshot.v),
  rooted wallet capture and exact execution authorization binding.
- **[F2]** [AuthorityPresentation.v](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/AuthorityPresentation.v),
  exact compound atom coverage, ordered head consumption, and residual suffixes.
- **[F3]** [LocatedStackConsumption.v](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/LocatedStackConsumption.v)
  and [LocatedAuthoritySettlement.v](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/LocatedAuthoritySettlement.v),
  located admission, history composition, and atomic settlement.
- **[F4]** [CanonicalCustodyAliasing.v](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/CanonicalCustodyAliasing.v),
  shared physical capacity, remaining balance, conservation, and wallet owners.
- **[F5]** [OrderedStackMaterialization.v](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/OrderedStackMaterialization.v),
  complete birth-event readiness and causal ordered stack histories.
