# Authored Cost(G) presentations: interpretation and proof obligations

An authored graph-structured lambda theory (GSLT) can name a cost algebra and
continued-interaction witnesses. Naming them does not prove their laws. This
document explains the formal connection required between those declarations
and the existing native cost-accounted Rholang semantics.

The [integration contract](oslf-integration-verification.md) describes the full
OSLF boundary. OSLF means *Operational Semantics in Logical Form*. The
[continued-GSLT manuscript](../../../../publications/cost-accounting-as-monad/continued-gslt-cost-v2.tex)
requires an interaction-cut presentation, a section of the term quotient, and
wrappability of the contraction on continuations. These are separate from
funding adequacy and native monetary settlement.

## What the checked refinement establishes

[`AuthoredCostInterpretation.v`](../../formal/rocq/rho_bridge/theories/AuthoredCostInterpretation.v)
composes existing native results. It defines no interpreter, parser, DDL
attribute, or runtime certificate format. Its source types and relations are
parameters, so the results are not tied to one guest grammar.

Let $`S`$ be the source-state type, $`L`$ the source-label type,
$`I:S\to\mathrm{signed\_term}`$ the state interpretation, and
$`J:L\to\mathrm{sig}`$ the grade interpretation. A source step
$`s\xrightarrow{\ell}t`$ must satisfy:

```math
s\xrightarrow{\ell}t
\quad\Longrightarrow\quad
I(s)\xrightarrow{J(\ell)}I(t).
```

The right-hand relation is the existing native `graded_step`, not a new
transition system. This forward-correspondence premise must cover every
source step to which the derived result is applied. A proof about one selected
example does not establish it for every installed rewrite.

| Result | Required evidence | Derived guarantee |
|---|---|---|
| `source_step_has_native_reduction` | Forward correspondence for the source step | Its interpretation is an actual native cost-accounted reduction. |
| `source_seal_blocks_every_step` | Forward correspondence and an interpretation equal to a lone `STSigned` wrapper | No source step can fire from that state without a corresponding native token-bearing context. |
| `source_whole_cut_keeps_exact_grade_and_continuation_seal` | Forward correspondence and the specified whole-cut native shape | The consumed grade is the outer signature; the successor retains the continuation's inner signature and exact residual stack. |
| `supplied_cimor_to_rho_preserves_no_leak` | An already established native `CIMor` into the Rholang object, with `mor_map morphism source = STSigned body authority` | The same no-leak result follows from that morphism's existing step-preservation field and the lone-seal shape. |

The proof reuses `graded_step_sound`, `no_leak_requires_token`, and
`whole_redex_step_has_exact_grade_and_residual`. It also includes a native
identity interpretation and a real funded step with distinct inner and outer
signatures. These establish that the conditional contract has a live instance.
They do not authenticate arbitrary authored declarations.

### Why a wrapped target type is not enough

Native `signed_term` syntax already ensures that native process bodies occur
inside wrappers. Accordingly, `well_wrapped_universal` applies to every value
of that type. Merely translating a guest term into `signed_term` proves no
operational restriction on the guest.

The no-leak result needs both the shape of the interpreted source state and
correspondence of its actual transitions. If a guest could take an unaccounted
step, forward correspondence would require a native step from a lone wrapper.
The existing native no-leak theorem rules that out.

This whole-cut result is not a classification theorem for every join,
surface geometry, or source equation. Those cases need their own valid
interpretation premises and can reuse the appropriate native results.

## Transporting the cost algebra's laws

The existing native [`CostMonad.v`](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/CostMonad.v)
defines `cost_eta`, `cost_mu`, and `cost_map`. Its grade combines a signature
with an ordered temporal token stack. Signature equivalence and stack equality
are not interchangeable.

The refinement has two levels:

1. **After interpretation.** The authored sides must interpret as the matching
   native expressions. The native left-unit, right-unit, and associativity
   theorems then establish `cost_equiv` between their interpretations.
2. **In the source theory.** For an explicitly declared law pair, the
   interpretation must also reflect the relevant source equivalence. Only
   then does native equivalence imply that source law.

Let $`D(x,y)`$ mean that the pair is a declared law, $`C`$ be the interpretation
into native cost values, $`\simeq_C`$ be native cost equivalence, and
$`\simeq_S`$ the claimed source equivalence. The reflection premise is:

```math
D(x,y)\land C(x)\simeq_C C(y)
\quad\Longrightarrow\quad x\simeq_S y.
```

Reflection is restricted to declared law pairs. The proof does not require
global injectivity or full abstraction for the entire guest language.
`source_left_unit_from_interpretation_and_reflection`,
`source_right_unit_from_interpretation_and_reflection`, and
`source_associativity_from_interpretation_and_reflection` use this premise.

The model includes a counterexample: an interpretation that maps both Boolean
values to one native unit value makes their interpretations equivalent while
the original values remain distinct. Therefore successful interpretation alone
cannot establish a source equation. The same distinction prevents the
[fixed-lane funding interpretation](finite-host-template-verification.md#funding-adequacy-is-not-quote-faithfulness)
from being treated as a quote-faithful behavioral morphism.

## Executable admission still has obligations

The conditional proof does not resolve `ContinuedDeclV1` or Cost(G) witness
strings. The current source-admission boundary must eventually establish:

- Exact installed source, rule, sort, constructor, and operation identities.
- The interaction-cut factorization and the interpretation of each covered
  source transition, grade, and wrapped continuation.
- The authored partial `compute` operation and its residual behavior.
- The authored `near` relation. Native channel equality is the Rholang
  instance, not a replacement for every guest's interaction surfaces.
- A section for the specified source quotient. A raw-representative
  commitment is not automatically such a section.
- Each claimed morphism's reachable-signature faithfulness and behavioral
  preservation, independently of its funding interpretation.
- Interpretation of the actual declared algebraic expressions and reflection
  for the law pairs being certified.

These are inputs to a sound composition, not proof obligations discharged by
string equality. Unknown or unresolved evidence must not authorize a checked
costed language. The existing
[source-row admission proof](oslf-integration-verification.md#exact-source-admission-and-grade-publication)
settles the narrower rewrite/grade-reference checks; it does not replace the
obligations above. This document introduces no new source syntax to encode
them.

## Verification evidence

On 2026-10-10, the proof and all twelve native dependency sources were rebuilt
under a 512 MiB memory cap, one CPU, and no swap. Independent `coqchk -silent`
passed. All thirteen primary assumption reports were closed. The log is
`target/verification/authored-cost-interpretation-20261010.log`.

The file is registered in the bridge's normal `_CoqProject`; its native
dependencies are included in the bridge Makefile's source selection.
The native instance and collapsing-interpretation example are checked by Rocq.
They are not Rust property tests. Source-specific executable properties cannot
be reported as passing until the corresponding admission implementation
establishes the premises above.

The complete integration's test results and remaining boundaries are recorded
in the [verification ledger](oslf-integration-verification.md#completion-criterion).
