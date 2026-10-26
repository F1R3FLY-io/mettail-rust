# Cost(G) to host funding: V2 selector proposal

Status (2026-10-10): the V2 contract is approved. Its precise DDL spelling
remains under review. The selector, compound-profile admission path, checked
selected-output projector, generated metered typed inverse, and independently
roster-checked Rholang compound codec provider are implemented. The finite
nullary-generator projection verifier is also implemented. Complete-roster
preparation has focused Rocq proofs and example/property tests. The installed
composition example and all 17 focused funding tests pass, including the
randomized owner and grade-sort checks. Full reachable host-carrier coverage,
authenticated protocol-7 RestingComm ingress, and live supply cutover
remain activation requirements. V2 funding is **not activated**. A matching
record or grade receipt alone conveys no funding authority. The existing
`ResourceProjectionV1` remains a declarative, non-funding record.

## Purpose and vocabulary

The [verification index](oslf-integration-verification.md) distinguishes the
component proofs from the complete native execution and replay obligations.

A graph-structured lambda theory (GSLT) may assign a **grade** to each rewrite:
an exact term in the theory's cost-signature sort. A grade says what a rewrite
consumed in the guest theory; it is not a host purse, a phlo charge, or proof
that execution is funded. A **projection** is an authored, typed GSLT relation
from a guest term to a host Rholang term. A **host demand bound** is a certificate
checked by Rholang's `OslfResourceLogic` against an independently authenticated
per-signature supply. OSLF means *Operational Semantics in Logical Form*; the
funding discipline is the distinct [cost-accounted rho calculus](rho-native-integration/references.md#cost-rho).
An **ABI** is a versioned application binary interface; **phlo** is the host's
unit of execution budget. An **exact ground key** is the checked structural
identity of a closed semantic term, not a serialization to parse as source.

The V2 contract makes the missing composition explicit: exactly one installed
GuestToHost relation is designated to interpret a checked guest grade as a
typed Rholang cost carrier. It does not make arbitrary projections funding
operations. The existing [OSLF compilation account](rho-native-integration/27-oslf-language-to-rholang-compilation.md)
explains the shared set-automaton pipeline; [the funding composition account](semantic-predicates/09-funding-composition.md)
explains why semantic evidence and funding evidence remain separate.

![Checked grade, selected projection, and host funding gates](figures/cost-g-funding-projection-v2.svg)

The editable [PlantUML source](figures/cost-g-funding-projection-v2.puml) names
the exact owners at every boundary.

## Existing boundary and the missing contract

`CostImageV1` binds each directed rewrite to a grade term in that rewrite's
original arena. The Dovetail kernel instantiates the successor and grade under
the **same substitution**, computes an exact ground key, and returns a checked
resource receipt. The projected compiler separately appends host signature and
relation programs to the original semantic image. Its `base_image_fingerprint`
and `base_rule_count` identify the original prefix. These two paths must be
composed without assigning a grade to an appended projection rule.

At installation, the Cost(G) image is fully validated against the exact
immutable source and base semantic image. A private installation witness pins
those objects, the admission-policy fingerprint, and the cost-image commitment.
Each live roster call borrows that witness after constant-time profile,
commitment, and projected-base checks; it does not repeat a full image
validation. The separately prepared matcher and grade-table access remain
resource-accounted. This witness authorizes reading checked grade roots only;
it cannot authorize host funding.

The V1 trusted Rholang host profile exposes generated ground `Bool`
and `Str` routes. Those are useful for predicates, not an exact transport for
`CostSig`, `CostStack`, or `Proc`. The current `ResourceProjectionV1` names
`grade_sort`, `demand_sort`, `project`, and `proof`, but has no executable
relation selector or trusted host endpoint; current validation even treats
both named sorts as guest sorts. Its bytes and meaning must stay unchanged.

| Boundary | Already available | V2 requirement |
|---|---|---|
| Guest rewrite | Checked Cost(G) grade, source-exact rule and substitution | Retain its projected e-graph root and exact key with the occurrence |
| Installed image | Checked base/projected prefix and an immutable, fully validated Cost(G) installation witness | Bind the future selector and host-carrier commitments to the same installed images without per-call full revalidation |
| Guest-to-host relation | Installed typed relation using the existing matcher | Select one relation explicitly for funding; retain every candidate |
| Host carrier | V1 Boolean/String codec and generated V2 compound routes | Complete reachable typed Rholang cost-carrier coverage, with the existing lowerer's contextual checks |
| Host judgment | `OslfResourceLogic` and authenticated per-signature supply | Verify the projected host demand bound against that supply; never infer supply from a grade |

## Proposed versioned selector

Define a **separate V2 envelope** around the existing projected-language V1
artifact. Do not add optional fields to the serialized V1 theory or change its
fingerprint. The envelope commits to:

1. the exact V1 projected-language and base semantic fingerprints;
2. one named, installed GuestToHost relation and its direction;
3. its input sort, equal to the declared Cost(G) signature sort;
4. its trusted host output category (a typed Rholang cost carrier) and exact
   host-signature and codec-profile fingerprints;
5. the accepted host resource-logic ABI and bound-verifier identity; and
6. the V2 envelope ABI and canonical digest.

The relation name is a selector, not a second rewrite language. Its rows remain
ordinary typed projection rewrites and run through the existing projected
set-automaton matcher. The current host `DefaultResourceLogic` checks canonical
`Par`, so the first executable selector must end in a typed `Proc` route that
lowers to `Par`. `CostSig` and `CostStack` are exact child carriers of that
route, not standalone funding programs. A future verifier may accept another
endpoint only through a new explicit ABI and checked lowering contract. The
selected-route profile does not claim that *all* recursively nested `Proc`,
`Name`, or `ForRow` values are transportable: each encountered child constructor
must be covered, or lowering refuses the value. The carrier must retain its
constructor tree and native value types; stringification, numeric narrowing,
and parsing an opaque grade key are forbidden. A signature value alone must
not be assumed to be a demand program: the selected endpoint must supply the
canonical `Par` which `OslfResourceLogic` actually checks.

Route coverage is weaker than fundability. For example, Rholang's current
iterative lowerer refuses a standalone `PForCostSigned`, and it handles
`CostSigTransfer` only in the signed-term context with an appropriate receive
continuation. The V2 route table must preserve those contextual refusals; it
cannot turn a syntactically recognized constructor into a funding proof.
Moreover, `CostSigHash` may contain any `Proc`, and `CostSigGround` may contain
any `Name`. Full V2 integration therefore requires a checked reconstruction
route for the complete reachable nested constructor closure, followed by the
existing typed lowerer's own acceptance check. A deliberately restricted
fail-closed subset could be useful, but it would not satisfy the full
integration contract and must not be reported as activated V2 support.

The familiar DDL relation syntax stays in `Rewrites`; the proposed funding
selector belongs in `Options`, not as another semantic rewrite. The precise
surface spelling is held for review. Conceptually, an author first declares a
relation such as `GradeToRhoCost : GuestSig ~> host::Proc` and then selects
`GradeToRhoCost` as the theory's funding interpretation. A theory may have
other projections of `GuestSig`; they do not gain funding authority. A missing,
multiply selected, reversed, mistyped, or unauthorized relation fails closed.

## Checked execution and ambiguity

The operation order is normative:

1. Verify the installed base, projected, cost, host-profile, and V2 selector
   commitments under the exact admission limits and required rights.
2. Execute the guest rewrite once with the existing Dovetail matcher. Retain
   both successor and grade e-classes from its one successful substitution.
3. Use the existing reachable-e-graph projector to admit the grade root as a
   relation input. Recompute its exact key and compare with the receipt; never
   decode or reparse the receipt bytes.
4. Execute only the selected GuestToHost relation under a charged work budget.
   Verify each result's input key, relation, direction, image, host-signature,
   codec, and proof commitments **before** invoking host demand computation.
   Preserve the complete candidate roster; exhaustion, not a fixed top-k
   prefix, is required to claim completeness.
5. Lower each checked typed host value through the trusted Rholang carrier
   route to canonical `Par`, then ask the existing host resource logic for a
   bound and independently verify that bound.
6. Obtain authenticated per-signature supply from the host offered-funded
   authority, not from the guest receipt or semantic work meter. Fund a
   candidate only when every required lane has sufficient supply. If an
   ambiguous roster is still enabled, do not select the first or cheapest:
   retain all alternatives and require each enabled candidate to pass before
   any shared commitment. A work-limit or cancellation result is not a
   complete roster and cannot fund. Otherwise remain undecided or refuse.

For a set of enabled candidates $`C`$, with checked host demand vector $`D(c)`$
and authenticated supply vector $`S`$, the safe shared-commit condition is:

```math
\mathsf{funded}(C,S)
\Longleftrightarrow
\mathsf{authenticated}(S)
\land \mathsf{complete}(C)
\land C\neq\varnothing
\land \forall c\in C,\;\bigl(\mathsf{checked}(c)
\land \forall \ell,\;D(c,\ell)\leq S(\ell)\bigr).
```

Here $`c`$ is one projection candidate and $`\ell`$ is one host signature lane.
This does not consume or reserve funds itself: the host's offered-funded
admission, price/limit policy, and settlement retain that authority. Guest
semantic work is charged separately even when projection or funding refuses.

### Base-image ownership and complete preparation

A projected installation has two language identities. The **base language**
owns the authored guest rewrites and their Cost(G) grades. The **projected
language** owns the installation envelope, host profile, and appended projection
relations. Their fingerprints normally differ. A base rewrite receipt must
match the sealed base image, not the projected installation's language
fingerprint. Conversely, a receipt labeled with the projected identity cannot
stand in for a base rewrite receipt.

Before projecting a one-step grade, preparation checks the base language,
theory, and image identities. It also checks that the receipt is a one-step
`Checked` grade with the installed grade sort and cost-image digest. The
existing reachable-root admission then checks the exact grade key. These
checks serve different purposes: root/key agreement does not authenticate the
claimed cost image or grade sort. A `CheckedTraceV2` receipt represents a
normalization trace and has separate ordered-hop obligations. It cannot be
relabelled as one-step evidence at this boundary.

Preparation retains each selected projection occurrence in its original order.
For example, two occurrences that produce the same host term remain two entries
with their respective receipts. The implementation reconstructs each typed
host value and lowers it through the existing Rholang converter. It uses one
cumulative work and payload budget for the complete roster. Empty results,
invalid candidates, exhausted budgets, and cancellation return an error, never
a successful prefix. Final owner checks precede returning the prepared roster.
Later funding and publication must still recheck live authority.

The [`BaseGradeRosterOwner` and `CompleteHostDemandRoster` models](../../formal/rocq/rho_bridge/theories/CostGradeFundingBoundary.v)
prove the corresponding abstract ownership, order, receipt, and work laws.
They assume the installed prefix witness and trusted matcher completeness.
They do not prove the complete Rust implementation or live consensus admission.
The [installed-path tests](../../rholang-runtime/src/semantic_service/funding_roster_tests.rs)
exercise the production finite verifier, generated host codec, guest rewrite,
selected projection, typed inverse, and canonical `Par` lowerer. The
[roster property tests](../../rholang-runtime/src/semantic_service.rs)
check ordered multiplicity, cumulative budgets, refusal, and cancellation.
These tests do not replace the full offered-funded replay gate.

## Compatibility, security, and validation gates

V1 `ResourceProjectionV1` stays readable with identical bytes, fingerprints,
and non-funding behavior. Uncosted and ordinary projected theories keep their
existing routes. Boolean/String predicate projections are unchanged. No
caller-supplied projection or receipt can install a host codec or mint supply.

Before V2 activation, verify all of the following:

- A bounded, zero-axiom Rocq refinement: same-substitution grade retention,
  exact key/root equality, base/projected prefix agreement, per-candidate
  image/codec/relation checks, and independent authenticated supply. The
  existing [cost-grade boundary model](../../formal/rocq/rho_bridge/theories/CostGradeFundingBoundary.v)
  covers the principal implications; the V2 implementation must refine it.
- Example and property tests for base/projected composition, typed carrier
  round trips, malformed/forged keys, wrong profile or ABI, missing/reversed
  selectors, ambiguous projections, and multiple host purse lanes.
- Independent compiled-route comparison of every selected category ID/tag,
  constructor ID/tag/discriminant, origin, and field schema. Checking only
  constructor names or a macro-generated digest does not authorize the V2
  candidate as a host codec.
- Full reachable nested-constructor reconstruction for typed `Proc`,
  `CostSig`, `CostStack`, `Name`, `InputBind`, and `ForRow` values, including
  arbitrary children of `CostSigHash` and `CostSigGround`, without changing
  contextual refusals in the existing iterative host lowerer.
- Check that live preparation borrows only the exact installation witness,
  charges matcher and grade-table work, and never repeats an unmetered full
  source/semantic/cost validation on each call.
- Differential checks that `MettaResourceLogic` and the host
  `DefaultResourceLogic` give identical demand, certificate verification,
  observation, and funding results for canonical signed/stack-bearing `Par`.
- End-to-end tests with offered-funded `phlo_price` and `phlo_limit` supplied
  by the client, with live/replay agreement and no guest authority escalation.
- A serial, memory-capped build/test run; no claim of activation merely because
  an image compiles or a proof receipt exists.

The proof and test obligations are not a substitute for a reviewed V2 DDL
spelling and trusted host-carrier ABI. Until both are accepted, Cost(G) receipts
remain semantic evidence only.
