# Ordered Cost(G) trace transport to host demand

## Status and trust boundary

This is a **formal transport model and pending implementation contract**, not
an assertion that multi-step trace funding is enabled in production. The
[Rocq model](../../formal/rocq/rho_bridge/theories/CostTraceFundingTransport.v)
reuses the exact [finite grade tree](../../formal/rocq/rho_bridge/theories/FiniteCostGradeFold.v)
and the [complete host-demand roster preparation](../../formal/rocq/rho_bridge/theories/CostGradeFundingBoundary.v).
It deliberately does not create a second evaluator, cost-image verifier,
projection matcher, native purse or settlement algorithm.

The [kernel's `CheckedTraceV2` receipt](../../dovetail-runtime/src/semantic_transition_kernel.rs)
contains an entry grade, final grade, and ordered normalization hops. Every
graded hop contains the *complete source-proof roster* and the selected proof
coordinate; each source proof has its own grade. The kernel constructs the
final grade as a left-associated product of the entry grade and selected hop
grades, in hop order, using the verified cost image's product constructor.
The ungraded parallel hop receipt is checked against the graded hop in
[`validate_fresh_transition_receipt`](../../rholang-runtime/src/semantic_service.rs):
length, endpoints, charged work, proof count, and exact proof bodies must agree.
The selected index must be within the graded roster. The plain hop has no
selected-index field. These are existing source checks, not a transport
proof to host demand.

```text
installed base/cost owner + checked trace receipt
  -> prepare the checked entry proof's complete host-demand roster
  -> check shared owner, every hop's ordered source-proof roster, selected index
  -> for each source proof: bind exact grade key to installed projected image
  -> prepare its entire GuestToHost candidate roster within the shared budget
  -> certify only if every required roster succeeds and final product matches
  -> retain the entry certificate and every ordered hop certificate
  -> hand the evidence to existing native authenticated funding (future seam)
```

In the model, a *source proof* is an alternative proof for one exact
normalization hop. A *host candidate* is an alternative result of applying the
installed GuestToHost relation to **that proof's** grade. Both multiplicities
matter: equal successor terms may have different proofs or grades, and one
grade may have several valid host projections. The boolean `roster_complete`
and `demand_proof_verified` fields are trusted outputs of their finite
verifiers; a caller must not set them merely because a visible prefix passed.

`proof_identity` represents the complete source proof, including its premises.
It is not an assertion that an arbitrary hash uniquely identifies a proof.
Each certificate retains this identity and the original selected index.
`trace_input` denotes the normalization start **after the entry rewrite**.
It is not the original action argument. The entry rewrite may already have
changed the term before the first normalization hop.

`trace_entry_proof_identity` identifies that checked entry derivation. The
entry certificate retains its grade and complete projected host-candidate list.
The existing transition receipt supplies the entry rule and premises. The
future adapter must bind these to the modeled entry identity and grade.
The model does not establish that correspondence from a numeric identifier.

## Formal obligations

For entry grade $`g_0`$, selected grades $`h_1,\ldots,h_n`$, and the installed
cost product $`\cdot`$, the receipt product is the ordered left fold:

```math
g_n = (((g_0 \cdot h_1) \cdot h_2) \cdots \cdot h_n).
```

The model uses `GradeProduct` as an exact syntax tree. It does **not** infer
that the semantic monoid is noncommutative: even if the installed quotient is
commutative, proof coordinates, receipt arrays, work charges and projection
rosters must not be silently sorted or deduplicated. With zero hops, the
result is exactly $`g_0`$, **not** a newly manufactured unit. A unit is valid
only when the already checked entry grade itself is the unit.

`certify_trace` checks the trace owner language, theory, retained base image,
cost digest and grade sort. Each source proof separately checks the shared
base/cost/sort owner and its selected projected image, relation, host handle
and exact key of that proof's grade. It then calls the existing
`prepare_host_demand_roster` model on the proof's **complete, nonempty** host
candidate roster. That roster model preserves output/receipt order and
multiplicity and rejects any failed candidate. A hop is certified only when
its exhaustive source roster is complete and the selected index is valid.
`prepare_hops` stages the ordered normalization sequence. `certify_trace`
returns the hop certificates after the final grade, endpoint, hop-roster work,
and cancellation checks succeed. This helper checks only normalization hops.
Its successful empty result does not certify the entry demand.

`certify_trace_with_entry` also requires the entry proof. It checks the entry
identity and exact grade, then uses `prepare_proof` for its complete host roster.
The wrapper retains the entry certificate beside the unchanged hop certificates.
Their combined roster work must fit one budget. Missing entry evidence,
mismatched entry identity or grade, and insufficient combined work all refuse.
A nonunit zero-hop trace still retains its checked entry candidates.

These certificates retain projected demand evidence. Native funding must still
establish the common supply witness and the applicable physical checks.
Rust's byte, allocation, reflection, and cancellation charges require separate
correspondence checks. The model's work sum accounts for candidate-roster work.

The file proves these directly checked properties:

| Theorem | Checked boundary | Required source-level property test |
|---|---|---|
| `prepare_proofs_exact_order`, `prepare_hop_exact_roster`, `certified_trace_preserves_order_and_multiplicity` | Every source proof and hop is retained in order; selected proof is in its original roster; emitted host term/receipt pairs come from complete roster preparation. | Construct two hops with duplicate successor terms but distinct proofs/grades and two host candidates for one proof; compare exact nested order and receipt multiplicity before/after transport. |
| `prepare_proof_exact_fields`, `prepare_proofs_identity_order`, `prepare_hop_preserves_proof_identity` | Exact source-proof identities, selected indices, grades, and complete host output/receipt lists are preserved. | Use equal grades with distinct proof bodies and repeated identical host candidates. Require exact nested lists, not sets. |
| `certified_trace_has_complete_checked_proofs_and_exact_fold` | Every hop has checked complete proofs. The final grade is the selected-grade left fold from the entry grade. Ownership, cancellation, and cumulative budget gates hold. | Compare the complete receipt with the transport result. Mutate the final grade, a projection owner, or a later candidate and require refusal. |
| `certified_trace_with_entry_has_complete_evidence`, `certified_entry_retains_exact_roster` | The complete transport retains the checked entry identity, grade, host roster, and receipts beside the ordered hop certificates. | Check a nonunit zero-hop trace and a multi-hop trace. Require the complete entry roster and its original proof identity. |
| `zero_step_preserves_entry_without_minting_unit` | The hop-only check preserves the entry grade. It does not certify entry demand. | Costed named-normalization action with no rewrite hop: require exact entry key; refuse a forged final unit or changed endpoint. |
| `missing_entry_has_no_complete_certificate`, `wrong_entry_identity_has_no_complete_certificate`, `wrong_entry_grade_has_no_complete_certificate` | The complete transport rejects absent or substituted entry evidence. | Remove the entry proof, change its identity, or replace its grade while retaining the original trace. Require refusal. |
| `entry_and_hops_share_one_work_bound`, `cancellation_has_no_complete_certificate` | Entry and hop preparation share one total work bound. Cancellation returns no complete certificate. | Use a budget sufficient for hops alone. Require refusal when the entry roster exceeds the remaining budget. Repeat with cancellation. |
| `wrong_trace_cost_digest_refuses`, `wrong_trace_grade_sort_refuses` | Whole-trace cost owner and grade sort cannot be substituted. | Mutate one receipt field at a time against the installed sealed commitment. Also mutate a per-proof base, cost, sort, projected image, relation, handle and grade key. |
| `exact_grade_product_retains_noncommutative_receipt_order` | Exact product-tree evidence distinguishes reversed selected hop order when grades differ. | Swap hop/proof order while retaining a forged final digest; require refusal, including equal-output/different-proof cases. |
| `cancellation_has_no_partial_certificate`, `insufficient_cumulative_work_has_no_certificate` | Cancelled or collectively unaffordable rosters have no trace certificate. | Fail the second candidate of a later hop after earlier preparation succeeds; assert no prefix certificate or native funding publication. Repeat with cumulative budget exhaustion/cancellation. |

The [existing service's one-step funding helper](../../rholang-runtime/src/semantic_service.rs)
`prepare_checked_host_demand_v2` currently accepts `SemanticResourceReceipt::Checked`
and rejects `CheckedTraceV2`; it does not iterate per-hop proof/host rosters.
The appropriate future seam is beside that helper, using its sealed installed
owner, retained exact-grade projection matcher, typed reconstruction, shared
`ReflectedCodecBudget`, and final revocation checks. It must not route a trace
digest or final aggregate through the one-step `admit_grade_at` path. The
kernel's [`compose_checked_grade_roots`](../../dovetail-runtime/src/semantic_transition_kernel.rs)
already owns the product; a transport adapter validates and carries its
evidence, not recomputes it with a generic analyzer.

## Checked results

The earlier hop-only model passed Rocq compilation and independent kernel
checking on 2026-10-10 under a 512 MiB memory limit. Eighteen assumption reports
were closed. Its log is `target/verification/cost-trace-transport-20261010.log`.

The entry-inclusive extension also passed `coqc` and independent `coqchk -silent`
checks on 2026-10-10. Both commands exited with code zero. All 31 printed
assumption reports were closed. The checks used a 512 MiB memory limit,
disabled swap, one CPU, and a 32-task limit. Both cached dependency sources
matched the current source before reuse. Only the trace source was recompiled.

The logs are `target/verification/cost-trace-entry-transport-20261010-coqc.log`
and `target/verification/cost-trace-entry-transport-20261010-coqchk.log`.
The successful silent kernel check produced an empty log. The checked source
SHA-256 is `023e59763ce9e210ef4cea885f72526636c5a83bca39dde83265424011cf2568`.

Seven closed examples exercise the hop-only helper:

- A two-hop trace preserves distinct equal-grade proofs, duplicate host receipts,
  and the selected proof coordinates.
- Dropping a hop refuses the resulting broken chain.
- Reordering the hops refuses the resulting broken chain.
- A fabricated final unit refuses a zero-hop trace with a nonunit entry grade.
- The authentic nonunit zero-hop trace produces an empty hop-certificate list.
- An insufficient cumulative budget returns no prefix certificate.
- Cancellation returns no prefix certificate.

Six additional examples cover the entry-inclusive transport:

- A nonunit zero-hop trace retains its entry identity, grade, and repeated host candidates.
- Missing entry evidence refuses a nonunit zero-hop trace.
- A substituted entry identity refuses.
- A substituted entry grade refuses.
- A budget sufficient for hops alone refuses when entry work exceeds that budget.
- A complete multi-hop trace retains the entry and normalization proof identities.

The fixture grade key is only a finite test encoding. It is not a cryptographic
codec or a proof of injectivity for arbitrary grade trees. The general lemmas
do not rely on that fixture encoding. The examples test the model, not a Rust
trace-to-funding adapter. The property tests listed above remain obligations
for that adapter's implementation.

## What remains unproved

The Rocq proof assumes that each required source-proof roster is exhaustive
and that each selected GuestToHost relation and its proof are valid.
It does not authenticate native supply. The planned Rust transport must map
the actual transition receipt, `CheckedTraceV2`, and retained grade roots to
the entry proof and every modeled hop proof. That mapping must retain each
exact grade key, projected commitment, duplicate occurrence, and complete host
roster. One cumulative reflected budget must cover both entry and hop rosters.
Any kernel `Undetermined`, cancellation, verifier refusal,
revocation, overflow or later host failure must leave no published prefix
certificate. Native supply, price/limit and consensus admission remain with
their existing authorities; this model grants none of them.

The finite grade fold guarantees occurrence accounting for the fixed
certified generator interpretation, not a general host funding law. The
separate conservative/equal host-demand law and full reachable closure still
need the selected interpretation's verified premise; an unbounded recursive
or higher-order source cannot acquire a finite bound by assertion.
