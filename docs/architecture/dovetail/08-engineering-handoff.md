# Engineering Handoff

This page is for an agent or engineer taking over Dovetail without prior
conversation context.

## Source Of Truth

| Area | File |
|---|---|
| crate overview | `dovetail/src/lib.rs` |
| exact keys | `dovetail/src/key.rs` |
| e-graph | `dovetail/src/egraph.rs` |
| rules and saturation | `dovetail/src/rules.rs` |
| WTA and cyclic closure | `dovetail/src/wta.rs`, `dovetail/src/scc.rs` |
| extraction | `dovetail/src/extract.rs` |
| reports | `dovetail/src/report.rs` |
| tuple-space seam | `dovetail/src/space.rs` |
| formal proofs | `dovetail/formal/rocq/theories/` |
| implementation plan | `docs/design/dovetail-engine/dovetail-core-implementation-plan.md` |

## Non-Negotiable Invariants

| Invariant | Engineering consequence |
|---|---|
| weights order, never prune | do not add beams, top-k cutoffs, or lossy heuristics |
| exact keys identify alternatives | do not replace `ContentKey` with a finite hash |
| completeness is terminal metadata | do not expose extraction as a plain iterator that loses `Done(completeness)` |
| cycles are explicit | do not report cyclic bounded extraction as `Complete` |
| saturation outcomes are explicit | do not collapse `Converged`, `NodeLimit`, and `IterationLimit` into a Boolean |
| Dovetail is substrate-agnostic | do not add parser, Ascent, Rho, or runtime dependencies to the crate |

## Adding A New Label Type

To use a new e-node label type `L`, the label must satisfy:

`Clone ∧ Eq ∧ Hash ∧ SemanticHash`

The `SemanticHash` implementation must write exact content bytes. For composite
labels, every variable-length part must be framed.

Handoff checklist:

1. Add or derive `Eq` and `Hash`.
2. Implement `SemanticHash` with framed composite fields.
3. Add tests showing distinct semantic labels produce distinct `ContentKey`s.
4. Add at least one extraction test using equal-weight distinct alternatives.

## Adding A New Weight Type

A weight used for extraction must satisfy:

`Semiring ∧ BestOrder ∧ MonotoneBestOrder`

`MonotoneBestOrder` is sealed. Extending it requires updating Rust marker
implementations and the proof/test story for monotonicity.

A weight used for cyclic closed inside weights must additionally satisfy:

`CommutativeStarSemiring`

That marker is also sealed. Extending it requires a commutativity argument and
closed-weight domain tests.

## Adding A New Rule Family

Literate pseudocode:

```text
To add a rule family:
  Model the left-hand and right-hand sides as Pattern values.
  Prove or test that every right-hand variable is bound by the left-hand side.
  Add an example saturation test for one concrete match.
  Add a negative test for an unbound or guarded-out match when applicable.
  Update requirement coverage if the rule family corresponds to a MeTTaIL feature class.
```

## Review Checklist

Before a Dovetail change is ready:

1. `cargo test -j1 -p dovetail` passes under the memory cap.
2. Property tests pass with an intentionally high `PROPTEST_CASES`.
3. `rocq-dovetail` passes under `formal/check-capped`.
4. Any changed Why3 or Creusot obligation passes its focused target.
5. The formal proof scan finds no new proof-hole or unchecked-premise markers.
6. Public extraction APIs preserve checked completeness.
7. Saturation still reports explicit terminal outcomes.
8. Documentation links and diagrams pass `docs/architecture/dovetail/validate.sh`.

## Integration Boundary

The Rho backend may consume Dovetail reports and lower covered rules to
`rhoapi::Par`. That does not make Rho a Dovetail dependency. The dependency
direction remains:

`dovetail → no runtime substrate`

`mettail-rho-codegen → dovetail semantics + f1r3node AST/runtime APIs`
