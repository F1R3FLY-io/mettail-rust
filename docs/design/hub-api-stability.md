# Hub API-Stability Hardening (Phase 4)

**Date:** 2026-06-21 · **Scope:** production-readiness campaign, Phase 4

The most-depended-on, highest-churn "hub" files were stabilised so churn stops
rippling through their dependents, **without breaking the public API**. This note
records what was done and — importantly — the two places where the honest
engineering answer was *not* to extract an interface, with the evidence.

## What was hardened

| Hub | In-deg / churn | Action | Result |
|·····|················|········|········|
| `ast/src/language.rs` | 202 / 7 | **Decoupled** the data model from the `syn` parser into `language/{model, parse}` behind a glob façade (see the split commit) | A parser-only edit now recompiles the leaf `parse` module, not the 1,850-line data model the 202 dependents resolve through |
| `prattail/src/type_system.rs` | 68 / 4 | **Trait boundary extracted** to `type_system/api.rs` (the `TypeSystem` trait), impls in sibling modules | An impl-body edit no longer dirties the trait's compilation unit |
| `prattail/src/automata` (subset.rs shotgun: 14 co-change partners) | 40 / 8 | **Absorbing boundary**: shared type vocabulary moved to `automata/types.rs` + `#[non_exhaustive]` on `TokenKind`/`TokenFamily`/`LexErrorKind`/`CharClass` | Algorithm modules consume a frozen types module; additive enum growth is non-breaking for external matchers |
| `prattail/src/gss.rs` (`EdgeKind`, 0→11 variants) | 163 / 18 | `#[non_exhaustive]` on `EdgeKind` | Future edge-kind additions no longer force lock-step `match` edits across the codegen + tests |

All four are behaviour + API preserving (façades / additive attributes), verified
by the full 7,837-test suite + a clean workspace build (all 202 `ast` dependents).

## Deliberate non-actions (with evidence)

The campaign's design principle is Occam's razor — *no abstraction for its own
sake*. Two hubs were analysed and intentionally **not** interface-extracted:

### `repl/src/repl.rs` (99 dependents, churn 26 — the highest churn) — DEFERRED
- Its public surface is already **one type** (`Repl` + 4 methods); there is nothing to extract.
- Every recent commit is *runtime-backend feature work* ("route REPL exec through backend reports", "make REPL state report-native", …); the diffs are inside private handlers reacting to `mettail_runtime` type changes. **The churn enters through imports, not through `Repl`'s surface** — an interface on `Repl` would not intercept it.
- The "99 dependents" are overwhelmingly intra-`repl` modules + its own test module; `repl` is effectively a leaf, so stabilising its interface yields ~zero ripple reduction.
- **Verdict:** interface extraction here would be the extract-interface cargo-cult. The real lever is upstream stabilisation of the `mettail_runtime` report/capability types (owned outside this hub scope, recorded for the runtime owner). Structural file-shrink of `repl.rs`'s private view/format layer remains available as a pure-structural follow-up if its size warrants it.

### `ast` `parse` feature gate — EVALUATED, NOT SHIPPED
- Proposal: gate `language/parse.rs` behind a `default = ["parse"]` feature so non-macro consumers (e.g. parts of `rholang-runtime`, `simulation`) skip compiling the `syn` parser.
- **Blocking fact (verified by reading the file):** `LanguageDef` and its sub-types carry `syn::Ident`, `proc_macro2::TokenStream`, and `syn::Type` **as data fields**. So `syn`/`proc-macro2` remain **non-optional** dependencies of the data model regardless of the gate; the gate would only remove the parser *code* compilation, not the `syn` crate, for non-macro consumers.
- **Verdict:** the marginal build-time win does not justify carrying a feature flag (which the design ethos treats as dead config when its benefit is unproven). Not shipped. If a future measurement (`cargo build -p <non-macro-consumer> --no-default-features` wall-clock) shows a real win, the gate is a one-commit addition.

### `gss.rs` deeper interface (trait over `WpdaGss`) — DEFERRED
- `WpdaGss<W: SemiringRef>` already abstracts over the weight via `W`; it is one actively-evolving impl. A trait over it would be premature (churn is legitimate GLR/WPDA algorithm development, not bad structure). The cheap, real win — making `EdgeKind` growth non-breaking — was taken (`#[non_exhaustive]`).

## Invariant preserved
`gss.rs`'s append-only edge-index stability contract (`GssEdgeId = (source << 32) | index`)
is unchanged; `#[non_exhaustive]` does not affect it.
