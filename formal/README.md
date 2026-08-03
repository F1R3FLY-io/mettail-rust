# Formal Verification

Run the active Prattail/WPDA proof and regression suite from the repository
root with a 32 GB cgroup memory cap:

```sh
make -C formal check-capped
```

## Verification Artifact Inventory

Every mechanized artifact relevant to Dovetail, the WPDA parser generator, the
RhoNet lowering, and the runtime wrappers, by tool and concern. All Rocq suites are
zero-admission (enforced by `rocq-critical-zero-admission`; ~154 `.v` across the 16
`formal/rocq` categories plus the relocated Dovetail Rocq tree).

| Tool | Location | Count | Primary concern (Dovetail / WPDA / RhoNet / wrappers) |
|---|---|---|---|
| Rocq — rho_bridge | `formal/rocq/rho_bridge/theories` | 42 | **RhoNet + wrappers**: install-boundary (`RhoLoweringTotalOrRejects`), host-obligation boundary (`RhoHostObligationBoundary`), COMM correspondence (`LinearCommCorrespondence`, `CommReductionCorrespondence`, `EndToEndCommCorrespondence`), flip gate, backend wrappers, artifact boundary, escrow/purse settlement |
| Rocq — prattail_wpda_runtime | `formal/rocq/prattail_wpda_runtime/theories` | 33 | **WPDA**: walker/recovery/dispatch models, lex-fork, cohort quotient, EOI delimiter windows |
| Rocq — symbolic_algebra | `formal/rocq/symbolic_algebra/theories` | 15 | predicate substrate: Heyting / effective-Boolean-algebra / guard-tier classification |
| Rocq — codegen_optimizations | `formal/rocq/codegen_optimizations/theories` | 13 | generated-codegen soundness, disjoint-first |
| Rocq — advanced_automata | `formal/rocq/advanced_automata/theories` | 12 | **positional set automaton** (`PositionalSetAutomatonSound`), MSO / register / PATA equivalence |
| Rocq — ascent_optimizations | `formal/rocq/ascent_optimizations/theories` | 7 | retired-Ascent-era optimization proofs |
| Rocq — trampoline | `formal/rocq/trampoline/theories` | 7 | Tier-3 held-fold trampoline soundness |
| Rocq — sft | `formal/rocq/sft/theories` | 6 | symbolic finite transducers |
| Rocq — mathematical_analyses | `formal/rocq/mathematical_analyses/theories` | 9 | KAT, exact VPA decisions/delimiters, and analysis soundness |
| Rocq — rule_consolidation | `formal/rocq/rule_consolidation/theories` | 5 | **Dovetail** disjoint-pattern consolidation |
| Rocq — egraph | `formal/rocq/egraph/theories` | 3 | **Dovetail** e-graph saturation |
| Rocq — lattice / logict / predicate_dispatch / presburger / unification | `formal/rocq/*/theories` | 1 each | supporting theories |
| Rocq — Dovetail suite | `dovetail/formal/rocq/theories/{ExactKeys,Extraction,InsideWeights,Lowering,Refinement,Requirements,Rigail,Saturation}` | (subdirs) | **Dovetail** engine: exact keys, extraction + weights, lowering, cyclic boundary, requirement inventory |
| TLA+ / Apalache | `formal/tla/{rho_machine,prattail_wpda,rho_settlement}` | 3 | Rho-machine COMM scheduling, WPDA control domain, per-purse settlement commutation |
| mCRL2 + Maude | `formal/process/` (generated from `rho_comm_slice.json`) | — | Rho COMM schedule / guarded-join non-consumption |
| Why3 + Creusot | `why3-dovetail-budget`, `creusot-dovetail-budget` | — | **Dovetail** budget obligations |
| Sage | `formal/sage/rho_net/rho_net_small_state.sage` (tool `/usr/bin/sage`) | #2049 | RhoNet small-state exploration: **matching** (positional root index = recursive oracle, 50 pattern×subject pairs), **observation** (SwapDemo σ-receiver lands `RHS[σ]`, non-vacuous), **scheduling** (independent-redex barb confluence); self-checking, runs under `sage` or `python3` |
| Wolfram | `formal/wolfram/rho_net/rho_net_small_state.wl` (Wolfram 15.0, `/usr/local/Wolfram/Wolfram/15.0/`) | #2049 | same three facets via native term rewriting (`Swap[x_,y_] :> Pair[y,x]`); self-checking, runs under `wolframscript`. Sibling patterns: cost-accounting (`f1r3node-cost-accounted-rho-calc`), fork-choice/finalized-floor (`f1r3node-rust-dev`) |

`make -C formal check` routes through the same capped target, so the default
formal verification entry point is protected as well. `check-capped` uses
`systemd-run --user` with `MemoryAccounting=yes`,
`MemoryMax=34359738368` (32 GiB), `MemoryHigh=30064771072` (28 GiB),
`MemorySwapMax=0`, `TasksMax=128`, `make -j1`, `CARGO_BUILD_JOBS=1`,
`cargo test -j1` for the Rust formal regression target, and the
repository-local `.formal-tmp` scratch directory. `FORMAL_MEMORY_MAX_BYTES` and
`FORMAL_MEMORY_HIGH_BYTES` may be lowered for tighter local runs, but
`check-capped` rejects any `FORMAL_MEMORY_MAX_BYTES` above 34359738368 bytes.
The capped service receives a deterministic `PATH` prefix through
`FORMAL_TOOL_PATH_PREFIX`, which defaults to the expected opam, TLAPS,
npm-global, cargo, and local user binary directories. The local user binary
directory covers locally installed Creusot/Alt-Ergo helpers such as
`alt-ergo` and `creusot-rustc`. Override `FORMAL_TOOL_PATH_PREFIX` when Rocq/Coq,
Apalache, Cargo, or the Creusot prover helpers are installed elsewhere.
The Maude process-calculus target exports `MAUDE_LIB=/usr/share/maude` by
default so capped non-login runs can locate `prelude.maude`; override
`MAUDE_LIB` only if Maude is installed in a non-system prefix.
The direct `check-uncapped` target always refuses to run; formal verification
must go through the capped entry point.
Direct verification subtargets and formal subproject Makefiles include
`capped.mk`, so they also refuse to run outside the capped wrapper. To run one
subtarget, pass it through `FORMAL_CAPPED_TARGET`, for example:

```sh
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-prattail-wpda
```

The Rocq directories whose primary `Makefile` is generated by `coq_makefile`
keep the cap policy in `GNUmakefile` and `Makefile.local`, so regenerating the
generated `Makefile` cannot remove the ordinary direct-build guard.
Generated `CoqMakefile` entry points include `CoqMakefile.local`; those local
files include the same cap policy, so explicit `make -f CoqMakefile`
invocations are guarded too. Clean targets remain allowed outside the cap.

The capped entry point runs:

- all Rocq proof suites under `formal/rocq`:
  `advanced_automata`, `ascent_optimizations`, `codegen_optimizations`,
  `egraph`, `lattice`, `logict`, `mathematical_analyses`,
  `prattail_wpda_runtime`, `predicate_dispatch`, `presburger`,
  `rule_consolidation`, `sft`, `trampoline`, and `unification`
- the relocated Dovetail Rocq proof suite under `dovetail/formal/rocq`
  (`FORMAL_CAPPED_TARGET=rocq-dovetail`)
- focused Dovetail enrichment targets:
  `rocq-dovetail-refinement`, `rocq-dovetail-requirements`,
  `rocq-dovetail-cyclic-boundary`, `why3-dovetail-budget`, and
  `creusot-dovetail-budget`
- focused Rho process-calculus targets:
  `mcrl2-rho-machine`, `maude-rho-machine`, `tla-rho-machine`, and
  `process-rho-comm-slice` (`process-rho-first-slice` remains as a
  compatibility alias). The mCRL2, Maude, and TLA+ files are generated from
  `formal/process/rho_comm_slice.json`, and the formal targets run
  `formal/process/rho_comm_slice.py --self-test` and
  `formal/process/rho_comm_slice.py --check` before model checking. The
  self-test validates malformed-spec rejection and the arity-parametric schedule
  derivation used by the generated finite projections. The generated mCRL2 and
  Maude slices cover both independent COMM schedules and guarded-join
  non-consumption after failed guard attempts.
- focused Rho settlement scheduler target:
  `tla-rho-settlement`, which TLC-checks bounded per-purse settlement
  commutation and fail-closed duplicate/missing-purse rejects.
- focused Rho bridge targets:
  `rocq-rho-bridge-artifact-boundary`, `rocq-rho-bridge-rejected-coverage`,
  `rocq-rho-bridge-lowering-boundary`, `rocq-rho-bridge-schedule-family`,
  `rocq-rho-bridge-cbn-budget`, `rocq-rho-bridge-delta1`,
  `rocq-rho-bridge-escrow-settlement`, `rocq-rho-bridge-purse-determinism`,
  and `rocq-rho-bridge-flip-gate`. `rocq-rho-bridge-delta1-matching`
  remains as a compatibility alias for the full Δ1 target.
- the critical Dovetail/Rho Rocq zero-admission gate:
  `rocq-critical-zero-admission`, which first runs the scanner self-test, then
  strips Rocq comments and rejects real `Admitted`, `admit.`, `Axiom`,
  `Conjecture`, `Parameter`, or `Parameters` commands under
  `dovetail/formal/rocq/theories` and
  `formal/rocq/rho_bridge/theories`
- Apalache checks in `formal/tla/prattail_wpda`
- the wrap-sensitive expected-counterexample harness
- the feature-gated Prattail WPDA walker Rust regression tests
- the WPDA macro-codegen unit tests
- generated-language WPDA smoke tests for cross-category infix dispatch and
  structural-delimiter collection parsing
- the Rholang lattice-token backend regression that verifies keyword text can
  still parse through identifier alternatives when the target category requires
  the variable rule

The formal Makefiles default `TMPDIR` to the repository-local `.formal-tmp`
directory and create it before invoking subtools. Override `TMPDIR` explicitly
only when you want a different non-tmpfs scratch location.

The active Prattail runtime proof directory includes:

- `RuntimeModel.v`: abstract cursor/config keys, dispatch keys, edge-kind
  wrap identity, quotient keys, EOI delimiter-window acceptance, and
  merge-weight algebra. (The former cursor-count *frontier-length* budget
  section — the `BeamSize`/`AmbiguityBudget` `cursor_bounding_mode` model and
  its R-D A1 engine-divergence note — was pruned in S6, 2026-07-15, together
  with the classic diagnostic engine it modeled; the production descriptor-pure
  engine enforces distinct-realized-term cardinality whole-run at resolve,
  validated behaviourally by the calculator/rholang flip-set rather than in
  this model.)
  Dispatch cache keys are modeled with full natural-number positions, with a
  generic obligation that distinct positions are not quotiented; Rust also
  exercises the concrete position above `u32::MAX` regression. The
  model includes the lex-alt postfix/infix/mixfix operator child transition
  and proves that the child advances to the selected alternative's next
  position while recording the lex-fork stamp; the same stamp is preserved on
  paused cohort return frames.
- `FiniteHarness.v`: Rocq justification for the finite TLA+ WPDA control
  domain and the deduplicated quotient-step model.
- `RecoveryBound.v`: the bounded-recovery state-space argument mirroring the
  Rust recovery fork gate: branch fanout is capped, retained branches either
  advance or carry an insert repair, strict parsing with max depth zero rejects
  recovery, child depth consumes the remaining recovery budget, and the same
  dispatch key is rejected after the child update. It also states explicit
  replay cursor-position obligations for multi-step repairs, direct
  insert/substitute/swap branch-target obligations, multi-effect target
  agreement, frontier and subtree-capacity bounds for the remaining recovery
  budget, the prefiltered-branch identity used by recovery dispatch candidate
  selection, the configured recovery-depth cache quotient used to avoid
  exact-depth state blow-up, negative recovery-beam normalization, recovery
  cost normalization to finite nonnegative search weights, the current
  two-candidate recovery synthesizer staying below the branch cap before the
  defensive cap path, recovery window bounds for past-end positions, plus the
  cache-invalidation obligation for token-source-mutating recovery replay.
  The packed-dispatch 40-bit position domain is kept as an opaque Rocq
  constant after its definition so proof search does not expand `2 ^ 40`; the
  theorem proves injectivity only for positions the Rust packer accepts.
- `RecoverySignature.v`: the exact outer token-map, outer sync-set, active
  recovery config, and nested WFST observations used by recovery dispatch
  cache keys. It proves that cache-key equality preserves the fields recovery
  branch synthesis observes, including the active max-recovery-depth override
  and configured depth-threshold observation. It also models recovery replay's
  token-source mutation predicate and proves that token-mutating replay clears
  the token-dependent dispatch/recovery/chain caches while cursor-only replay
  preserves them, without discarding dispatch or recovery diagnostic
  registration counters. The file also records the runtime driver obligation that
  every walker-owned `engine.step` path pins both the recovery cohort cache and
  the active recovery config, so generated recovery dispatch observes the
  walker config rather than falling back to category-local defaults.

The EOI delimiter-window obligation mirrors
`WpdaWalker::is_cursor_accepting_terminal_at`: same-span semantic roots accept
directly only inside the token source; a shorter semantic root may be accepted
at EOI only when the omitted prefix is all structural open delimiters, the
omitted suffix is all structural close delimiters, and both windows are exact
in-bounds token-source windows. The runtime applies this theorem only when the
token source advertises linear token positions; `LatticeTokenSource` positions
are DAG node ids, so it does not scan numeric node-id intervals as token
windows. Rocq proves that non-structural prefixes and out-of-range linear
windows are rejected.
