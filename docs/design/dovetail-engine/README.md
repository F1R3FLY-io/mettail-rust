# Dovetail Engine — Design-of-Record

This directory holds the **design-of-record** documents for the Dovetail rewrite
engine and the Rho-bridge bring-up: the original, code-grounded plans authored by
Plan agents as the engine was built (2026-06-09 onward). They capture *why* each
increment was shaped the way it was, the rejected alternatives, and the
verification obligations.

> **Read these as design history, not as the current contract.** Where a design
> doc overlaps the published architecture suite, the published suite is
> authoritative. Each doc below carries a reconciled status line noting what
> shipped. The pedagogical, current-state description lives in
> [`docs/architecture/dovetail/`](../../architecture/dovetail/README.md) (the
> standalone engine) and
> [`docs/architecture/rho-native-integration/`](../../architecture/rho-native-integration/README.md)
> (the Rho machine integration).

## Documents

| Document | Subject | Published counterpart |
|---|---|---|
| [`dovetail-core-implementation-plan.md`](dovetail-core-implementation-plan.md) | Foundational crate plan: the `rigail`/`dovetail` split, public API, the governing extraction-completeness invariant, and the increment sequence. | [`02-engine-architecture`](../../architecture/dovetail/02-engine-architecture.md) |
| [`semiring-extraction-plan.md`](semiring-extraction-plan.md) | Increment 1 — extracting the weight algebra into the lower `rigail` crate behind a `prattail` facade (executed). | [`05-extraction-and-weights`](../../architecture/dovetail/05-extraction-and-weights.md) |
| [`extractor-design.md`](extractor-design.md) | Increment 5 — the Huang–Chiang lazy `k`-best extractor and the no-miss argument. | [`05-extraction-and-weights`](../../architecture/dovetail/05-extraction-and-weights.md) |
| [`cyclic-closure-design.md`](cyclic-closure-design.md) | Increment 6 — Newton–SCC exact cyclic inside-weight closure and the cycle-cut enumeration boundary. | [`06-cyclic-closure-and-boundedness`](../../architecture/dovetail/06-cyclic-closure-and-boundedness.md) |
| [`lazy-ac-matching.md`](lazy-ac-matching.md) | In-engine lazy associative-commutative rewrite matching: canonical `par`-bag lowering and the `AcApp` `OpenRule` path. | [`04-rules-and-saturation`](../../architecture/dovetail/04-rules-and-saturation.md), [`11-binder-congruence-handler`](../../architecture/dovetail/11-binder-congruence-handler.md) |
| [`oslf-gslt-native-fold-reduction.md`](oslf-gslt-native-fold-reduction.md) | The theory of Dovetail as the foundational funding/GSLT engine and the native-fold reduction (typed-`L` op-enum, the funding discipline). | [`12-native-fold-reduction`](../../architecture/dovetail/12-native-fold-reduction.md) |
| [`m-rho-0-implementation-plan.md`](m-rho-0-implementation-plan.md) | M-RHO.0 — the Rho-bridge bring-up (the three bridge crates, funding conformance re-hosting, calculator-to-`Par` lowering). | [`rho-native-integration`](../../architecture/rho-native-integration/README.md) |

## Status

All seven plans have shipped. Dovetail is the live general-purpose production
rewrite backend (enabled through the `languages` crate's default `dovetail-codegen`
feature), and the Rho-native lane is live through the renamed
`rholang-codegen` / `rholang-runtime` / `rholang-adapter` bridge crates. The
generated Ascent engine and the CESK runtime backend were retired in P6.
