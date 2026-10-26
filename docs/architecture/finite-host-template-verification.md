# Finite host template: authority accounting and source correspondence

The accepted finite interpretation maps every guest generator to signed
`Nil` with the actual quoted-`Nil` signature. The unit maps to empty `Nil`.
Products combine signatures through the native signature operation. They do
not create parallel signed processes or acquire supply.

The [installed checker](../../grammar-core/src/finite_grade_projection.rs)
accepts the exact typed template `PCostSignedTerm(PZero, CostSigHash(PZero))`.
This restriction prevents an authored projection from adding hidden sends,
receives, or supply-bearing bodies.

## Formal result

[FiniteHostTemplate.v](../../formal/rocq/rho_bridge/theories/FiniteHostTemplate.v)
reuses the [finite grade tree](../../formal/rocq/rho_bridge/theories/FiniteCostGradeFold.v)
and native `payable_sig_atoms` and `exact_cover`. An authority atom is one
nonunit signature component. An exact cover preserves every atom's multiplicity.

Let $`g`$ be a finite grade. Let $`I(g)`$ be its native signature interpretation.
Let $`q`$ denote the encoding of canonical quoted `Nil`, and let $`n(g)`$ count
generator occurrences. The interpretation maps unit to `SUnit`, generators to
`SQuote q`, and products to `SAnd`.

```math
\mathrm{atoms}(I(g))
  = [\mathrm{SQuote}(q)]^{n(g)}.
```

The exponent denotes list repetition, not multiplication of monetary charges.
Repeated generators remain repeated authority atoms. Alternative projection
candidates are not added together by this theorem.

| Theorems | Established fact |
|---|---|
| `native_grade_atoms_match_finite_interpretation`, `native_grade_preserves_quoted_nil_multiplicity` | The native signature retains exactly the existing finite interpretation's generator occurrences. |
| `native_grade_unit_is_neutral`, `native_grade_product_keeps_all_atoms` | Unit and product preserve the intended signature algebra. |
| `native_template_exactly_covers_grade`, `native_nonunit_template_is_one_whole_cell` | The existing nonunit template represents one compound cell containing every required atom. |
| `canonical_template_preserves_exact_cover`, `canonical_funding_retains_every_atom` | Atom-preserving native canonicalization and an exact cover retain every required atom, with no omission or amplification. |

The last row assumes `canonical_signature_for`: canonicalization preserves
payable atoms up to permutation. This is an explicit source-refinement premise,
not a proved property of the Rust implementation. The parameter `nil_quote`
must denote the actual canonical quoted-`Nil` encoding. The proof makes no
hash-injectivity assumption and does not define another demand analyzer.

### Funding adequacy is not quote-faithfulness

Generator identity and generator multiplicity are different properties.
For distinct generator identifiers $`a`$ and $`b`$, this interpretation gives:

```math
I(\mathrm{Generator}(a))
 = \mathrm{SQuote}(q)
 = I(\mathrm{Generator}(b)).
```

It retains one payable occurrence in either case, but does not distinguish
the two guest identifiers. This is intentional for the accepted fixed-lane
funding interpretation. Its checked result is exact coverage of the
*interpreted host demand*, not injectivity of the guest-to-host map.

A continued-interactive GSLT morphism has a separate quote-faithfulness
requirement. Native
[`CIMor`](../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/CACategory.v)
requires its signature map to be injective on the source object's reachable
signature fragment. The fixed-lane interpretation cannot supply that evidence
when two distinct reachable generator signatures map to the same host atom.
A behavioral morphism must establish quote-faithfulness independently; this
funding certificate must not be relabeled as that proof. No change to the
accepted template, signature codec, or settlement rules follows from this
distinction.

## Executable property correspondence

[finite_host_template.rs](../../rholang-adapter/tests/finite_host_template.rs)
uses actual `Quote(Par::default())` signatures and native
`compound_cost_signatures`. Iterative finite-forest generation varies product
shape, generator multiplicity, and unit placement. No recursive test evaluator
or new production interpreter is introduced.

The tests call both `DefaultResourceLogic` and `MettaResourceLogic`, including
their real canonicalization and bound-verification paths. They require:

- Every retained nonunit atom is the actual quoted `Nil`.
- Product reassociation, permutation, and unit insertion preserve the canonical signature.
- The unit has an empty `FiniteUpperBound`.
- A nonunit template has one bound unit on its whole compound signature lane.
- Both verifiers accept the recomputed bound.
- Changed amounts, changed proof bytes, and promotion to `Exact` are rejected.

For example, two generators require one layer on the compound lane containing
two quoted-`Nil` atoms. They do not require two layers on the original atomic
lane. Native prefix coverage must retain both atoms inside that compound layer.

The expected lane rule follows the existing native analyzer's empty signed
region branch in `delta_sigma.rs`. The tests check that source correspondence;
the Rocq file does not prove correctness of the Rust analyzer or wire codec.
Neither file claims arbitrary-program analyzer soundness, arbitrary authored
projection adequacy, or a native firing of signed `Nil`.

## Verification and remaining boundary

Run the focused property suite only within the repository's resource-capped
verification lane. Do not run this command in an uncapped shell:

```sh
cargo test -p rholang-adapter --test finite_host_template
```

The formal file uses the existing `RhoBridge` and `CostAccountedRho` logical
paths. On 2026-10-10, `coqc` and independent `coqchk -silent` both passed.
All thirteen assumption reports were closed. The proof gate used a 512 MiB
memory cap, one CPU, and no swap. Its log is
`target/verification/oslf-final-model-checks-20261010.log`.

All three executable tests passed. These include two property families with
128 generated cases each, plus the finite examples. The ten resource-logic
parity tests also passed in the same serialized run. Cargo used one job under
a 32 GiB memory cap with no swap. The log is
`target/verification/oslf-template-and-parity-20261010.log`.

Runtime integration must still establish exact installed-template ownership,
retained-grade correspondence, canonical lane identity, and authenticated
native-prefix coverage. This algebraic bridge does not publish state, settle
money, manufacture authority, or close an unbounded source execution.
