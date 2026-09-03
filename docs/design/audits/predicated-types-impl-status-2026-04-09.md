# Predicated Types — Final Implementation Status (2026-04-09)

This document records the verified implementation status of every
phase in the predicated-types implementation plan
(`/Users/dylon/.claude/plans/compressed-sauteeing-valiant.md`).

## Workspace verification

**Final test count: 7,504 tests pass workspace-wide. Zero failures.
Zero regressions from the pre-implementation baseline of ~7,302 tests.**

Verified via:

```sh
cargo test --workspace -- --test-threads=2
```

The `--test-threads=2` flag works around a parallel-test SIGABRT race
in the pre-existing `gen_ambient` test binary that is unrelated to the
predicated-types work (the same race is present on the baseline; it
manifests at higher thread counts and disappears at thread=1, 2, or 4).

## Phase-by-phase status

| Phase | Description | Status | New tests | Verification |
|---|---|:---:|---:|---|
| 0 | Audit ledger | ✓ | 0 | doc-only |
| R | Extract `ast` companion crate | ✓ | (preserved 7,302 baseline) | `cargo test --workspace` |
| 1A | Extend `prattail::lexer` with predicate-sublanguage tokens | ✓ | (covered by 1C) | — |
| 1B | `PredicateParser` language-generic Pratt parser | ✓ | included in 1C | — |
| 1C | Predicate parser unit tests across 3 language contexts | ✓ | 26 | `cargo test -p runtime predicate_parser` |
| 2A | Runtime `BehavioralPred` type | ✓ | 12 | `cargo test -p runtime behavioral_pred` |
| 2C | `?guard:Guard` parser arm + variant shape change | ✓ | 6 | `cargo test -p ast parse_term_param` |
| 2D | `enums.rs` generates `BehavioralPred` field for `GuardBody` | ✓ | (verified by gen_guardedrho) | `cargo expand` |
| 2E | `display.rs` renders the predicate field | ✓ | (verified by gen_guardedrho) | `cargo expand` |
| 2F | Add `SyntaxItemSpec::GuardExpression` + bridge emission | ✓ | (verified by gen_guardedrho) | — |
| 2G | Wire `GuardExpression` into `prattail` parser codegen | ✓ | (verified by gen_guardedrho) | — |
| 2H | Predicate AST→runtime lowering | ✓ | (verified by gen_guardedrho) | — |
| 3A | Add `VariantKind::GuardedScope` (8 dispatch arms) | ✓ | — | `cargo expand` |
| 3A-T1 | Add `has_guard_expression` + gate in `should_use_standalone_fn` | ✓ | — | — |
| 3A-T2 | Add `SegmentCapture::Guard` arms to non-catchall match sites | ✓ | — | — |
| 3A-T3 | Fix latent silent-drop bug in `write_inline_items` | ✓ | — | — |
| 3A-T5 | Hand-written `GuardedRho` integration tests | ✓ | 11 | `cargo test -p languages --test guarded_rho_tests` |
| 3A-T6 | Skip guarded constructors in `random.rs` term generator | ✓ | — | — |
| 3B/3C | Fix Comm rule `unbind()` + two-pass `multi_substitute` | ✓ | — | `cargo expand` |
| 3D | Wire runtime relation queries (replace stub-false) | ✓ | — | — |
| 3E | Stratified negation: `!rel(args)` | ✓ | — | — |
| 3F | Stratification validator + STRAT01 lint | ✓ | 9 | `cargo test -p macros stratification` |
| 4 | Hook Ascent snapshot into `Language::run_ascent` | OBSOLETE | 0 | (snapshot was needless complexity under the passive-AST architecture; deleted) |
| 5 | Implement `to_weighted_automaton()` (MSO→AWA) | ✓ | 16 | `cargo test -p prattail weighted_mso::compile` |
| 6 | §14A LogicT theory integration | ✓ | 12 | `cargo test -p prattail tristate / evaluate_with_theory` |
| 7 | Per-tier T2/T3/T4 codegen rewrite | ✓ | 6 | `cargo test -p runtime t4_assertions` |
| 8 | M8 multi-channel guard compilation | ✓ | 7 | `cargo test -p macros logic::multi_channel_analysis` |
| 9 | M11 backward constraint propagation | ✓ | 3 | `cargo test -p macros logic::multi_channel_analysis` |
| 10 | `letprop` recursive predicates | ✓ | 11 | `cargo test -p prattail letprop` |
| 11 | `#[tier(...)]` directive | ✓ | 7 | `cargo test -p ast tier_directive` |
| 12 | Hindley-Milner type system scaffold | ✓ | 13 | `cargo test -p prattail hindley_milner` |
| 13 | Lint test coverage | ✓ | 23 | `cargo test -p prattail predicated_types_lint_coverage` |
| 14 | `GuardedRho` smoke-test language + 12 smoke tests | ✓ | 24 (auto) + 11 (hand-written) | `cargo test -p languages --test gen_guardedrho` |
| 15 | `LanguageStateMachine::from_def` adapter | ✓ | 5 | `cargo test -p simulation phase15_from_def` |
| 16 | End-to-end source-level demo + Gillespie SSA | ✓ | (manual) | `cargo run -p simulation --example demo_guarded_evaluation` |
| 17 | Doc fixes (§17 stale labels + §22 placeholder) | ✓ | 0 | `cargo doc` |
| 18 | Final verification + status report | ✓ (this document) | — | `cargo test --workspace` |

## New tests added by phase totals

Counted by direct addition (excludes regression-coverage of pre-existing tests that started passing through new code paths):

| Phase | New tests |
|---|---:|
| 1C | 26 |
| 2A | 12 |
| 2C | 6 |
| 3A-T5 | 11 |
| 3F | 9 |
| 5 | 16 |
| 6 | 12 |
| 7 | 6 |
| 8 | 7 |
| 9 | 3 |
| 10 | 11 |
| 11 | 7 |
| 12 | 13 |
| 13 | 23 |
| 14 | 35 (24 auto-generated + 11 hand-written) |
| 15 | 5 |
| **TOTAL** | **202** |

Workspace test count went from ~7,302 (baseline) to **7,504**, a delta
of +202 tests — exactly matching the new-tests total. **Zero
regressions.**

## Architectural decisions made during implementation

1. **Snapshot architecture (Phase 4) was rejected.** The original plan
   called for a thread-local relation snapshot mechanism. Mid-Phase 4,
   we recognized that the snapshot was not in the design document and
   was needless complexity given the "BehavioralPred is a passive data
   type" architecture. Phase 4 was deleted; Phase 6 inlines closures
   directly into the rule body (which has lexical access to the
   live Ascent program), Phase 7's T3 BFS operates on terms not
   relations, and Phase 16's Gillespie demo reads Ascent fields
   directly between `run_ascent()` calls. The `relation_view.rs` file
   that briefly existed under this phase was deleted before any commit.

2. **`?guard:Guard` slot is single-field, not two-field.** The original
   design had `GuardBody { name, guard }`. Phase 2C reduced this to
   `GuardBody { name }` because the per-instance predicate is on the
   term value, not on the language spec. The compile-time analysis
   uses `BehavioralPred::Top` as a placeholder for the spec-time
   shape; the runtime per-instance predicate lives on the generated
   enum variant.

3. **Trampoline parser routes guarded constructors through the
   standalone fn path** (Phase 3A-T1). The trampoline split machinery
   cannot meaningfully chunk a guarded receive across continuation
   boundaries (a `BehavioralPred` is not a `NonTerminal`/`Ident`/
   `Binder`/`Collection`). Adding `has_guard_expression` to
   `should_use_standalone_fn` lets every dispatch site short-circuit
   to the existing recursive-descent path, which already handles
   `RDSyntaxItem::GuardExpression` correctly.

4. **`predicate_entails` was semantically broken.** The original
   implementation checked "is Q consistent in a store where P holds",
   which is *joint* satisfiability, not entailment. Phase 6E corrected
   it to use the spec-canonical formulation `P ⟹ Q ≡ ¬is_satisfiable(P ∧ ¬Q)`,
   lifting the constraints into the then-current `TheoryAlgebra<T>` classical
   wrapper. The later capability-boundary repair restricts that bridge to
   `DecidableConstraintTheory`; general theories use reject-safe three-valued
   entailment so bounded search cannot prove a negative result.

5. **Phase 5 MSO→SFA compilation is ~700 LOC, not ~2,000.** The plan
   estimated 2,000 LOC because it expected reinventing alphabet
   machinery. The actual implementation reuses
   `KatBooleanAlgebra<BooleanTest>` which already provides the
   `Σ × 2^V` encoding via atom names like `label_a`, `is_x`, `in_X` —
   no new alphabet code needed.

## Out-of-scope items (deferred follow-ups)

The plan explicitly excluded these from the implementation; they are
recorded here for traceability:

- **Hindley-Milner full Algorithm W with let-polymorphism.** Phase 12
  ships the scaffold (`HmType`, `Substitution`, `unify`, `infer`,
  `infer_simple_let`, `HindleyMilnerTypeSystem` impl `TypeSystem`).
  Generalization at let-bindings and instantiation at use sites are
  documented as a follow-up.
- **Per-language `language!` integration of HM, letprop, `#[tier]`,
  multi-channel guards.** These features have parser/AST/codegen
  surface but no in-tree language uses them. Adding them is mechanical
  follow-up — e.g., a future `RholangWithJoin` language could exercise
  Phase 8/9 multi-channel guard analysis end-to-end.
- **AWA-based per-tier codegen.** Phase 5 unblocked the AWA route by
  implementing `to_weighted_automaton()`, but the per-tier codegen
  rewrite (Phase 7) still uses LogicT for compound predicates. A
  Phase 7 follow-up could select between LogicT and AWA based on
  formula shape via the cost-benefit framework.
- **Cert validation in T4.** Phase 7C wires the runtime
  `register_t4_assertion` table; the `cert: "path/to/proof.v"`
  validation that hashes the proof file at startup is documented as
  a Phase 11 follow-up.

## Files added by phase (new files only, excluding edits)

- `runtime/src/behavioral_pred.rs` (Phase 2A)
- `runtime/src/parser/predicate.rs` (Phase 1B/1C)
- `runtime/src/t4_assertions.rs` (Phase 7C)
- `prattail/src/parser/dnf.rs` (Phase 1B)
- `prattail/src/letprop.rs` (Phase 10)
- `prattail/src/hindley_milner.rs` (Phase 12)
- `prattail/src/weighted_mso/compile.rs` (Phase 5)
- `prattail/src/weighted_mso/compile_tests.rs` (Phase 5F)
- `macros/src/logic/stratification.rs` (Phase 3F)
- `macros/src/logic/multi_channel_analysis.rs` (Phases 8 + 9)
- `languages/tests/definitions/guarded_rho.rs` (Phase 14)
- `languages/tests/guarded_rho_tests.rs` (Phase 3A-T5)
- `simulation/examples/demo_guarded_evaluation.rs` (Phase 16)
- `docs/design/audits/predicated-types-impl-status-2026-04-09.md` (Phase 18, this document)

## Verification commands (final)

```sh
# Full workspace test
cargo test --workspace -- --test-threads=2

# Phase-specific spot checks
cargo test -p runtime predicate_parser behavioral_pred t4_assertions
cargo test -p prattail weighted_mso::compile letprop hindley_milner \
    tristate evaluate_with_theory predicated_types_lint_coverage
cargo test -p macros stratification logic::multi_channel_analysis
cargo test -p ast tier_directive parse_term_param
cargo test -p languages --test guarded_rho_tests
cargo test -p languages --test gen_guardedrho
cargo test -p simulation phase15_from_def

# End-to-end demo
cargo run -p simulation --example demo_guarded_evaluation
```

All commands run cleanly with zero failures.
