# 14 — Rho-Native Campaign — Completion Audit

> pgmcp plan #1956 (`complete-rho-native-dovetail-rho-parser-generator-and-runtime-architecture-refactor`).
> This is the final completion audit (Epic 1 #2078) with its supporting change
> classification (#1970) and requirement to evidence matrix (#1972/#1973). It records,
> per epic, the authoritative evidence for each delivered requirement so the persistent
> goal can be verified against current code. Branch: `codex/rho-native-set-automata`.

## 1. Method (#1973 evidence discipline)

Every claim below cites **authoritative evidence** of one of these kinds: a **commit**
(the change), a **test** (behavioral proof, run under the capped `ci` nextest profile),
a **formal proof** (`.v`, zero-admission — `Print Assumptions` = "Closed under the
global context"), a **benchmark** (criterion, CCD0-pinned, governor `performance`,
t-test p<0.05), or a **generated artifact**. North star: *every rewrite executes on
Rholang save semantic predicates* (per `../../../publications/knotted-topoi/`), with
matching optimized by the set-automaton papers.

## 2. Change classification (#1970)

28 first-parent campaign commits since the fork, by top-level concern:

| Concern | Files | Representative commits |
|---|---|---|
| Documentation | 18 | #2002, #2065, #2043, #2068 (+ tail), this audit |
| Generated languages | 13 | SwapDemo (R-4/R-5), Calculator/Rholang runtime tests |
| Dovetail engine | 12 | O1 FxHash, O2/O3 extraction, set-automaton |
| rholang-runtime | 10 | sigma-injection bridge, install boundary, F-stage |
| Formal (Rocq/Sage/Wolfram) | 9 | Epic 8 FVs, #2049 models |
| macros (codegen) | 8 | RhoNet to Par lowering, report codegen, #2030 accessor |
| rholang-codegen | 6 | RhoNet planning, install-boundary Result |
| runtime / repl / testkit / ... | 8 | routing, capability backends, harness |

Every change classifies to **Dovetail matching/saturation**, **RhoNet planning/
lowering**, **runtime backend/bridge**, **formal verification**, or **documentation** —
none touches the WPDA parser generator (that is the primary tree's domain, kept disjoint
to minimize merge conflicts; the one merge had a 1-file conflict surface).

## 3. Requirement to evidence matrix, by epic (#1972 / #2078 verification)

### Epic 4 — RhoNet lowering + sigma-injection bridge (north star)
| Requirement | Evidence | Verified |
|---|---|---|
| RhoNet to `Par` lowering codegen | commits `ad6e2f00`, `98cbffa0` (constructor reflection) | ✅ |
| Runtime sigma-injection bridge (Dovetail to sigma to Rho) | `922ef9dc` + `rholang-runtime/tests/rho_net_equivalence.rs` (SwapDemo `Swap(A,B)` to `Pair(B,A)` on a live Rho machine) | ✅ |
| Per-rewrite sigma in the Dovetail report | `597ca1e2` | ✅ |
| Fail-closed install boundary | `06e091a5` (`installed_program_par` to `Result`) + `RhoLoweringTotalOrRejects.v` `Section RhoNetInstallBoundary` | ✅ proof |
| Model-b faithfulness (matching locus is a free choice) | `aefa8327` doc 13 (14 invariants); the paper proves CLTS-level correspondence | ✅ |
| End-to-end operational correspondence | per-step `LinearCommCorrespondence.v` + **`EndToEndCommCorrespondence.v`** (finite-trace lift, `2a96926d`, zero-admission) | ✅ proof |

### Epic 5/6/7 — runtime-invocation split, accessors, REPL
| Requirement | Evidence | Verified |
|---|---|---|
| Runtime invocation migration (`DeferToDovetailReport` to `DeferToDovetailSemanticPredicate`) | doc 12 (`8f8467ed`); no-silent-host-fallback invariant | ✅ |
| Generated `rho_net_program()` accessor + codegen-determinism/boundary tests | `7696b52e` (#2030/#2033) | ✅ tests |
| REPL routing across all bundled languages | capability backends (prior campaign) | ✅ |

### Epic 8 — formal verification (Deep-FV, user-prioritized)
| Requirement | Evidence | Verified |
|---|---|---|
| Positional set-automaton = recursive oracle (non-AC) | `PositionalSetAutomatonSound.v` (`3c36d29a`, zero-admission) + `dovetail/tests/properties.rs` oracle | ✅ proof + test |
| AC-matching separation (AC rejected to lazy path) | same FV (`ac_pattern_not_compilable` / `structural_pattern_compilable`) | ✅ proof |
| Compiled-rule-set reuse | `reuse_is_per_node_deterministic` + `compiled_rule_set_reuses_positional_automata_across_graphs` | ✅ proof + test |
| Host-obligation boundary (semantic-predicates-only) | `RhoHostObligationBoundary.v` (`c161b39f`, #2048) | ✅ proof |
| FV artifact inventory | `formal/README.md` inventory table (`82499902`/`4ad5400c`, #2043) | ✅ |
| Sage/Wolfram RhoNet small-state models | `formal/{sage,wolfram}/rho_net/` (`20e4701e`, #2049) — both self-check + pass | ✅ artifact |

### Epic 9 — performance (baselines to optimization, data-driven)
| Requirement | Evidence | Verified |
|---|---|---|
| Baselines + scientific ledger | `rho_native_bench` + `docs/benchmarks/rho-native-baselines.md` (`43b16d0d`, #2053) | ✅ |
| O1 FxHash e-graph keys | `8a86435a` — saturation -24...-40%, t-test p<0.05, 113+306 tests | ✅ bench + test |
| O2 extractor reuse across roots | `bbc05217` — -17...-28%, 3563 tests | ✅ bench + test |
| O3 composed-derivation reuse | `ad95ddfa` — -10...-16%, oracle-verified byte-identical | ✅ bench + proof-test |

### Epic 10 — documentation
| Requirement | Evidence | Verified |
|---|---|---|
| Set-automaton matcher doc | dovetail doc 14 (`9e384e48`/`6831148b`, #2065), validator passes | ✅ |
| Diagrams/examples synced with code (no stale fallback) | `42ab454e` + `ad6daf6e` (#2068 core + tail) — zero stale `DeferToDovetailReport` refs remain outside doc 12's intentional history | ✅ |

## 4. Routed to the primary tree (explicit user directive — separation of concerns)

Per the user's explicit instruction ("keep this tree focused; let the primary tree
optimize the WPDA parser backend; request parser changes, I will make them"):

| Item | Status |
|---|---|
| **fix #1** — demand-gate cross-category numeric injection (`calculator.rs`) | change request delivered to the user for the primary tree; the engine-side complement (O2/O3) is landed here |
| uint32 cast-roundtrip + Epic 2 WPDA parser | primary-tree domain (root-caused, recorded) |
| proc/bool/float `*_display_parse_roundtrip` timeouts | primary-tree ROOT-P repair (pre-existing, not merge-introduced) |

## 5. Remaining in-tree (tracked, #1974)

Epic 11 housekeeping only: log sweep (#2075) and the 109 G sibling build-target
reclamation (#2076, session-end). No functional or verification requirement is open in
this tree.

## 6. Verdict

Every in-tree requirement of plan #1956 is delivered with authoritative evidence:
**functional** (Epic 4-7 bridge + boundary + accessors), **formal** (Epic 8 — four
zero-admission Rocq FVs + two self-checking Sage/Wolfram models + the end-to-end opcorr
lift), **performance** (Epic 9 — three t-test-gated, oracle-verified generic engine
optimizations), and **documentation** (Epic 10 — matcher doc + full stale-reference
sync). The parser-generator surface is intentionally untouched and routed to the primary
tree. The persistent goal is complete in this tree modulo the explicitly primary-tree-routed
parser items and Epic 11 housekeeping.
