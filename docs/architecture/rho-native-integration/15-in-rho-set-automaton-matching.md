# 15 — In-Rho Set-Automaton Matching Integration

> **Campaign.** Finish Greg Meredith's unfinished set-automaton matching
> integration: compile the two set-automaton papers' automaton (plus the
> `[optimal]` channel-naming scheme, `docs/papers/optimal-channels.tex`) INTO the
> Rho execution, so pattern matching is `O1`-optimal (symbol-once) and runs ON the
> Rholang interpreter (f1r3node `RhoRuntime`/`RSpace`), with every
> non-semantic-predicate rewrite firing as one atomic COMM. Approved plan:
> `floofy-rolling-shore`; pgmcp epic `in-rho-set-automaton-matching-integration`.
> This document is authored incrementally, one campaign stage per section.

## 1. The execution model

`knotted-topoi.tex` fixes correctness at the context-labelled transition system
(CLTS): a base rewrite $\llbracket L \Rightarrow R \rrbracket$ firing at location
$\ell$ is exactly one atomic COMM rendezvous on the location channel
$c(\ell) = \ulcorner \ell \urcorner$ emitting $\llbracket R \rrbracket \sigma$:

$$ \llbracket L \Rightarrow R \rrbracket(c) \;=\; \mathtt{for}\bigl(\llbracket L \rrbracket \Leftarrow c\bigr)\bigl\{\, c!\bigl(\llbracket R \rrbracket\bigr) \,\bigr\} $$

The campaign realizes this in three layers, each faithful to the same CLTS:

1. **Matching** — the host `SetAutomaton` is compiled into a network of persistent
   `sa:` receivers over a *spread* term $\llbracket t \rrbracket$; head-symbol
   dispatch via `Match`/`MatchCase`; non-linear consistency via enable-guarded
   `eq:` receivers. These run on the Rholang interpreter as internal
   ($\tau$, unobservable) COMMs. The channel for a context $K$ is the reflected
   suspended automaton trace $tc(K) = \ulcorner T_M(K) \urcorner$; the host's
   `PatternCompiler::intern` already computes the paper's `O1`+`O3` quotient, so
   re-keying `sa:` channels by the interned `StateId` trace *is* the optimal
   scheme.
2. **Firing** — on an accepting match, the automaton emits $\sigma$ on the rule's
   channel and the flat $(k+1)$-ary $\sigma$-receiver fires the observable
   $c(\ell)$ COMM producing $\llbracket R \rrbracket \sigma$.
3. **Congruence and predicates** — equations compile to compile-time structural
   congruence (never a COMM); semantic predicates are the sole off-machine class,
   evaluated by an Effective-Boolean-Algebra / native handler.

The load-bearing correctness result is the discharge of the tex's asserted
`rem:nonopt` claim — that the sound (location-channel) scheme and the optimal
(set-automaton-state) scheme induce the *same* CLTS: `O1`-totality plus
$tc$-injectivity (with the outermost-preserving relation $R_{op}$) yield a
weak bisimulation in which the internal `sa:`/`eq:` steps erase to $\tau$.

## 2. Stage 0 — the firing driver (host-matched stepping stone)

Stage 0 wires the *firing* half as the multi-firing execution path, with matching
still host-side (the current, formally-faithful model-b). It is a stepping stone
that Stage 1 supersedes by moving matching into Rho; the firing layer it
establishes is reused unchanged.

### 2.1 One firing = one COMM

The host Dovetail report already carries, in firing order, the substitution
$\sigma_i$ of every rewrite firing (`report.rewrite_justifications`). The Stage 0
driver realizes the CLTS at the granularity of these firings: for each firing it
composes the installed $\sigma$-receiver program with a $\sigma$-injection `call`
and observes the result on the interpreter, so every non-semantic-predicate
rewrite of a multi-step reduction executes as one atomic $c(\ell)$ COMM.

```
report.rewrite_justifications        install σ-receiver program ONCE
   [ σ₀ , σ₁ , … , σ_{n-1} ]     ┌─────────────────────────────────┐
        │  per firing i          │  installed_rho_net_program_par  │
        ▼                        └─────────────────────────────────┘
  reflect σ_i → call_i  ───────────────▶  installed ∥ call_i   (fresh RSpace)
        │                                        │  atomic COMM
        │                                        ▼
        └───────────────────────  observe  ⟦R⟧σ_i  on OUT_i
```

Because the host report has already computed every $\sigma_i$, each firing is an
independent atomic COMM against the persistent $\sigma$-receiver — a faithful
*replay* of the report's firings on the interpreter. The whole-program normal
form remains the host-extracted e-graph root (structural congruence /
plugging is not itself a COMM), consistent with the tex leaving the whole-GSLT
`opcorr` obligation open.

### 2.2 Implementation

| Piece | Location |
|---|---|
| Indexed $\sigma$-injection surface | generated `<Lang>::rho_net_invocation_from_dovetail_to_firing(term, report, out, i)` (`macros/src/gen/runtime/rho_invocation.rs`); the single-firing `…_from_dovetail_to` delegates at index 0 |
| Full replay sequence | generated `<Lang>::rho_net_replay_invocation_from_dovetail_to(term, report, prefix)` — one injection per firing; an empty result is a normal form (a valid no-op), unlike the single-firing method which fails closed |
| Replay bridge | `build_rho_net_replay_invocation_from_contracts`, which builds `RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { firings }` (`rholang-runtime/src/backend.rs`) |
| Replay driver | `PlannedRhoBackend::run_rho_net_replay_and_observe_runtime_values` — installs the $\sigma$-receiver program once, fires each firing as its own COMM, collects every $\llbracket R \rrbracket \sigma_i$ |

The path is **capability-gated and fail-closed**: the driver installs the
$\sigma$-receiver program via `installed_rho_net_program_par` *before* any Rho
reduction, so a language whose rules do not all lower surfaces at the install
boundary, never as a silent runtime no-op.

### 2.3 Verification

- **Example / integration** (`rholang-runtime/tests/rho_net_equivalence.rs`):
  `Pair(Swap(A, B), Swap(B, A))` yields two *distinct* firings (structurally-equal
  redexes hash-cons to one e-class); the driver fires both and observes
  `Pair(B, A)` and `Pair(A, B)`, each equal to its report-derived
  $\llbracket R \rrbracket \sigma$. The generated wiring and the normal-form
  no-op case are covered separately.
- **Property-based**: for arbitrary well-formed SwapDemo terms, the replay
  observations equal — in firing order — the report's per-firing
  $\mathrm{Pair}(\sigma[y], \sigma[x])$; this exercises the
  $\sigma$-reflection / injection round-trip across the full space of $\sigma$
  shapes (nested terms give nested $\sigma$).

Stage 0 introduces no new formal-verification obligation (it reuses the proven
per-step base-rewrite correspondence). The `O1` symbol-once matching, its
correctness proofs, and the in-Rho `sa:`/`eq:` compilation are the subject of the
following stages.
