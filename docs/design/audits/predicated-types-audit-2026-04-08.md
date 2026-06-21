# Predicated Types — Implementation Audit (2026-04-08)

This document is the honest, code-grounded gap analysis of
`docs/design/predicated-types.md` (9,820 lines) against the actual
state of the workspace. It exists because the previous claim that the
design was fully implemented was incorrect, and that misrepresentation
needs a written record so it does not happen again.

The audit is structured by section, mirroring the design document.
Each section reports:

- **Spec** — what the doc specifies
- **Code status** — one of EXISTS / PARTIAL / MISSING / DEAD CODE / INCONSISTENT
- **Evidence** — file:line citations
- **Gap** — what is still required for the design to be honored

## Executive Summary

| Layer                                           | Status                                                                                                                            |
|-------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------|
| **§§1–3** Conceptual / formal definitions       | ✓ doc-only                                                                                                                        |
| **§4** PGuardedInput term shape                 | PARTIAL — variant exists, field count wrong (3 vs spec's 4), no parse path                                                       |
| **§5** Pattern matching algorithm               | ✓ 95% — `MatchBindings`, `MatchTask`, iterative engine, 7 VariantKind arms; minor collection-ordering deviation                   |
| **§6** Guarded Comm rule (auto-generation)      | PARTIAL — `generate_guarded_comm_rules` exists with 5 specific bugs; structural rule cannot bind guard variables                 |
| **§7** Worked end-to-end example                | NO TEST FIXTURE — no language uses PGuardedInput                                                                                   |
| **§7A** Architectural overview (5 subsystems)   | ✓ all 5 exist                                                                                                                      |
| **§8** Behavioral predicates                    | PARTIAL — positive Ascent join works; negation stubbed; quantified relation/domain callbacks stubbed `false`/empty; AcMatch ✓     |
| **§10** Parser steps for `where` clause         | **0%** — no `where` keyword tokenization in any user-source parser; only syn-based proc-macro parser exists                      |
| **§11** Decidability tiering                    | ✓ structural; 2 parallel enums; SFA-based T1 elimination missing                                                                  |
| **§12** Five-stage pipeline                     | PARTIAL — Parse stage **0%**; Classify ✓; Compile **0%** (no `to_weighted_automaton()`); Optimize ✓; Codegen ✓                    |
| **§13** Guard compilation strategies            | PARTIAL — T2 Ascent join works; T1 stub; T3 brittle heuristic; T4 stub; `#[tier(...)]` missing; `letprop` missing                  |
| **§14** Compile/runtime boundary                | ✓ architecturally                                                                                                                  |
| **§14A** LogicT theory integration              | **0% wired** — `TheoryAlgebra<T>`, theories, `predicate_entails` all exist but never invoked from guard pipeline                  |
| **§15** BooleanAlgebra framework                | ✓ **FULLY IMPLEMENTED** (3,747 LOC, 91 tests)                                                                                      |
| **§16** Constraint theory suite                 | ✓ **FULLY IMPLEMENTED** — Presburger 2,988 LOC/94t, Unification 2,163/70t, Lattice 2,145/49t, LogicT 2,368/75t                    |
| **§17** Modules M1–M15                         | ✓ **ALL 15 EXIST**. M2/M3/M4 marked "design only" in doc but actually implemented (2K-3.5K LOC each)                              |
| **§18** Composition for FOL                     | PARTIAL — propositional ✓; quantifier composition unimplemented because `to_weighted_automaton()` is missing                      |
| **§19** Lint integration                        | PARTIAL — 30 lint IDs declared+emitted; only RT01-RT06 tested; TIER01/DNF01/TOK01/MT03/STRAT01 missing                            |
| **§20** Pluggable type system                   | PARTIAL — `TypeSystem` ✓; `Lattice`/`Refinement`/`SetTheoretic` ✓; `predicate_entails` divergent; HM absent                       |
| **§21** Implementation architecture             | ✓ tokens + guards both implemented                                                                                                 |
| **§22**                                         | **MISSING from doc** — section number skipped from §21 → §23                                                                       |
| **§23** References                              | ✓ doc-only                                                                                                                         |

Total estimated implementation: ~40% of the design end-to-end. The
infrastructure layer (§§15–17) is largely real (~31,000 LOC of
working code). The orchestration layer that connects user-source
`where` clauses to the existing infrastructure is largely missing.

## Critical findings

1. **`TermParam::GuardBody` parser path is MISSING.** `parse_term_param`
   in `ast/grammar.rs:472` only handles `Simple`, `Abstraction`, and
   `MultiAbstraction`. No `?` token branch exists. **No code
   anywhere constructs a `TermParam::GuardBody` value** — verified
   by grep. The 25 downstream sites that pattern-match it are
   unreachable from any user-written `language!` invocation.

2. **`enums.rs:295` emits ZERO fields for `GuardBody`.** Comment:
   "Guard bodies do not generate enum variant fields." But
   `rules.rs:2209-2213` destructures 3 fields, neither shape matches
   the doc's 4-field spec.

3. **No `where` keyword tokenization anywhere.** Search for `"where"`
   in `prattail/src/` only finds it as a Rust keyword in
   `automata/codegen.rs:3753`'s denylist. There is no
   `parse_where_clause`, no `WhereClause` AST type, no
   `prattail/src/parser/` directory at all.

4. **`to_weighted_automaton()` is the linchpin and is unimplemented.**
   Both `weighted_mso.rs:249` and `guard_codegen.rs:36` self-document
   this. Its absence cascades into: no SFA-driven T2 codegen, no
   SFA-emptiness-based T1 elimination, no SFA-intersection guard
   fusion, no exact satisfiability/overlap analysis enhancement.

5. **The §14A theory bridge is fully unwired.** Trait, theories, and
   `TheoryAlgebra<T>` exist, but `evaluate_quantified` ignores them
   and there is no `evaluate_quantified_with_theory`. T1-via-`predicate_entails`
   and Unknown-refinement are both missing.

6. **`#[tier(...)]` directive is entirely absent.**

7. **`letprop` is entirely absent.** No parser, no mu-calculus
   lowering, no PATA bridge from user code. `mu_calculus_to_pata`
   exists at `parity_tree.rs:700` but is reachable only from tests.

8. **Negated behavioral predicates are stubbed** (`rules.rs:725-745`):
   they emit `if { … true }` instead of Ascent's `!rel(args)`. This
   is unsound at runtime.

9. **Quantified guards' inline relation/domain callbacks are stubbed**
   to always return `false`/empty (`rules.rs:670-675`). The standalone
   `__guard_N` functions would work if called externally, but they
   are not wired into Ascent rule bodies.

10. **The structural Comm rule uses `inner()` + `unsafe_body` instead
    of `unbind()`** (`rules.rs:2223-2232`). Guard pattern variables
    become `BoundVar`s, not `FreeVar`s, so `match_pattern` cannot bind
    them. The structural rule as written is functionally broken even
    if its precondition were ever satisfied.

11. **Continuation substitution loops single-var instead of vectorized
    `multi_substitute_name` then `multi_substitute`**
    (`rules.rs:2247-2255`). Doc spec says vectorized two-pass.

12. **`PredArg::Constant` carries `Ident`, not a ground `Proc` term.**
    Ground-term constants like `{}` cannot be passed as predicate
    arguments.

13. **All 30 non-RT lints have ZERO test coverage.** Only RT01-RT06
    (refinement type lints) have dedicated unit tests.

14. **Hindley-Milner type system is completely absent** despite §20
    claiming "infrastructure already available". The `TypeSystem`
    trait, `UnificationTheory`, and `TypeSystemAlgebra<S>` exist, but
    no `HindleyMilnerTypeSystem` struct.

15. **`macros` is `proc-macro = true`.** Demos cannot
    `parse2::<LanguageDef>(quote!{ … })` because non-proc-macro
    consumers cannot import types from a proc-macro crate. An
    architectural refactor (extract `ast` companion crate)
    is required for any non-proc-macro consumer of `LanguageDef`.

## What IS solid (and will be reused)

- §15 BooleanAlgebra framework — `SymbolicAutomaton`, all 6 algebras,
  minterm-determinization, ProductAlgebra. 3,747 LOC, 91 tests.
- §16 Constraint theory suite — Presburger / Unification / Lattice
  all fully implemented with 213 tests across 7,296 LOC.
- §17 Modules M1–M15 — every single file exists with substantial code
  and test coverage. Total: 31,461 LOC across the 15 modules.
- §5 Pattern matching algorithm — `MatchBindings`, `MatchTask`,
  iterative engine, 7 of 8 VariantKind arms.
- LogicT (`evaluate_quantified`, `QuantifiedFormula`, multiset_partitions
  for AC-matching) — 2,368 LOC with 75 tests.
- `Language::parse_term`, `Language::run_ascent`, `AscentResults`
  trait surfaces — already exist at `runtime/src/language.rs:120-126,229`.
- `StochasticPetriNet::from_channel_metadata`, `gillespie_ssa` —
  already exist at `simulation/src/stochastic_petri.rs:281,314`.
- The `guards { connectives, theories, channels }` block parser —
  fully wired at `language.rs:2213+`.

Total reusable infrastructure: ~75,000 LOC of working, tested code.

## Implementation plan

The plan to close the gaps is at
`/Users/dylon/.claude/plans/compressed-sauteeing-valiant.md`. It
covers 18 phases adding ~10,800 LOC of new code and ~700 LOC of bug
fixes on top of the existing infrastructure. The plan is grounded in
this audit and is structured so that each phase has a verifiable
test gate.

## Per-section detailed audit

The full per-section audit (§3 through §22) is captured in the
exploration agent reports embedded in the conversation transcript at
`/Users/dylon/.claude/projects/-Users-dylon-Workspace-f1r3fly-io-mettail-rust/af235994-5626-40b2-93f1-c7492f61c555.jsonl`.
Key per-section findings are preserved in the executive summary
table above. The transcript contains:

- §3-§7A audit (2026-04-08, ~1,500 lines of structured findings)
- §8 and §10 audit (2026-04-08, ~1,500 lines)
- §11-§14A audit (2026-04-08, ~1,200 lines)
- §15-§18 audit (2026-04-08, ~1,200 lines)
- §19-§21 audit (2026-04-08, ~1,300 lines)

These per-section audits will be consolidated into structured
appendices in a follow-up task once the implementation phases land.
For now this executive summary plus the implementation plan is
sufficient to drive the work forward.
