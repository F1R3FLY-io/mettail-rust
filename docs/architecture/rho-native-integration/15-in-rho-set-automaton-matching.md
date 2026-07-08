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

## 3. Stage 1 — matching in Rho

Stage 1 moves the MATCHING onto the interpreter: the host `SetAutomaton` is
compiled into a network of `sa:` receivers that consume a *spread* subject and, on
an accepting match, hand the substitution to the Stage 0 firing layer. Recognizing
a redex is now itself a sequence of Rho COMMs (the internal, `$\tau$`-labelled
symbol inspections), not a host computation. The flow is shown in
Figure [15-1](figures/15-in-rho-matching-flow.svg).

### 3.1 The spread subject (M0)

A ground subject term is spread across per-location channels
(`spread_term_par`, `rholang-codegen/src/rho_net_lower.rs`):

$$ \llbracket f(t_1,\dots,t_n) \rrbracket_\ell \;=\; c(\ell)!\bigl(\underline{f}\bigr) \;\Big|\; \prod_{i} \llbracket t_i \rrbracket_{\ell\cdot(f,i)} $$

Each node publishes ONLY its head tag `$\underline{f}$` on its deterministic quoted
location channel `$c(\ell)$`; the child locations `$\ell\cdot(f,i)$` are derived,
never carried in the message. The scheme is `$\nu$`-free (INV-7): a flat parallel
composition of ground sends — no `New`, no `BoundVar` — the resolved Option-B of
the design, faithful to `def:loc` and `rem:fresh`.

### 3.2 The automaton network (M1)

`automaton_receiver_network_par` (`rholang-codegen/src/rho_net_automaton.rs`)
serializes a single App-rooted, linear `SetAutomaton` into the receiver network.
Each interned state becomes ONE `for`-receive — the `$\tau$` symbol inspection of
the two set-automaton papers — over its location channel; the received head tag is
`Match`-dispatched on the state's constructor; and the accepting configuration
sends the substitution tuple on the rule's channel:

$$ \mathtt{for}\bigl(h \Leftarrow c(\ell)\bigr)\bigl\{\; \mathtt{match}\ h\ \{\; \underline{f} \Rightarrow \dots \Rightarrow c!(\sigma_0,\dots,\sigma_{k-1}, @\mathit{out}) \;\} \;\bigr\} $$

The accept send is byte-identical to the message the Stage 0 `$\sigma$`-injection
builds, so the EXISTING persistent `$\sigma$`-receiver fires unchanged and lands
`$\llbracket R \rrbracket\sigma$`. The De Bruijn frame is exact: the accept is free
in `$\{0,\dots,k-1\}$`, each `for`-wrap shifts the free set under its binder, the
`Match` re-adds its `$\mathrm{BoundVar}(0)$` target, and the root `for` closes the
network; the substitution slot for the `$i$`-th argument is
`$\mathrm{EList}[\mathrm{BoundVar}(k-1-i)]$`.

The interned-state key is the `O1`/`O3` quotient: structurally-equal sub-patterns
share one `StateId`, hence (Stage 1 M2) one `sa:` receiver — the `[optimal]`
scheme's channel sharing, already computed by the host interner. Out-of-scope
shapes fail closed (`AutomatonUnsupported`): multi-pattern, non-linear variables,
nested-App / non-nullary Var subtrees, and bare-variable roots each route to a
later slice rather than emitting an incorrect network.

### 3.3 Validated in Rho

`m1_matches_swap_in_rho_and_fires_the_rewrite` (`rho_net_equivalence.rs`): the
compiled automaton matches `Swap(A, B)` ON the interpreter (the `$\tau$` `sa:`
COMMs over the spread — the host does NOT inject the substitution) and fires the
rewrite to `Pair(B, A)`. Because `Swap(A, B)` differs from `Pair(B, A)`, a positive
`OUT` is non-vacuous evidence the match happened in Rho, and the RSpace reducer
validates the De Bruijn / `locally_free` frame end-to-end — which a structural test
alone cannot. The negative case `m1_does_not_match_a_non_matching_head_in_rho`
confirms a wrong head (`Pair` vs `Swap`) does not accept: no false-positive match.

The Phase-A correctness proofs (`SymbolOnceInjective`, `InRhoMatchPositional`,
`InRhoReuseDeterminism`) verify this single-pattern matching core; §3.4 extends it to
multiple patterns, and the `sa:`/`eq:`-as-`$\tau$` same-CLTS discharge (M3 — the
`rem:nonopt` weak bisimulation) is the remaining Stage 1 obligation.

### 3.4 Multi-pattern dispatch (M2a)

`automaton_receiver_network_par`'s multi-pattern generalization
(`multi_pattern_receiver_network_par`) serializes one or more App-rooted linear entries
into ONE network sharing a single root `loc:` receive. The linear single-shot spread publishes
each node's head tag exactly once, so only one `for`-receive can consume it: the root
tag is received once and `Match`-dispatched — ONE case per distinct root op, the reified
`app_roots` router (`search_egraph`'s dispatch). Entries sharing an op share the child
`for`-receives — the interned `StateId` quotient means structurally-equal sub-patterns
share one state, hence one receiver — and on accept the network announces in PARALLEL to
each rule's channel `$c!(\sigma, @\mathit{out}_e)$`, the `O3` "share the match, announce
to every rule" fan-out. The M1 single-pattern serializer is the special case (one entry
gives one `Match` case, the byte-identical M1 frame), so `automaton_receiver_network_par`
delegates — no dual path.

Validated in Rho (`rho_net_equivalence.rs`): a `Swap(A, B)` subject against a
`[Swap, Pair]` network fires ONLY the Swap accept (the router discriminates on the head
tag, so `OUT` carries exactly `[A, B]`); two rules sharing the LHS `Swap(x, y)` fire BOTH
accepts (`OUT` carries `[A, B]` twice — the fan-out). Out-of-scope shapes fail closed:
`ConflictingArityForOp` (one `Match` case cannot host two arities — a typed algebra never
produces it, since the op determines the arity), `MissingAcceptTarget`, plus the retained
non-linear / nested-App / bare-variable-root rejections.

The channel-NAMING for the shared receivers — re-keying `pattern_trace_channel` from the
whole-LHS identity (the paper's rejected `@K` naming) to the interned-state trace
`$tc(K) = \ulcorner T_M(K) \urcorner$` — is verified as the unique `O1`/`O3` quotient by
`TcChannelNamingQuotient` (viii) and applied in production by M2b.

### 3.5 The `sa:`/`eq:` steps are `$\tau$` — the same-CLTS discharge (M3)

The in-Rho matching's `sa:` (symbol inspection) and `eq:` (non-linear consistency)
COMMs are INTERNAL — unobservable `$\tau$` steps — so moving matching into Rho does
not change the observable behavior. `knotted-topoi.tex` ASSERTS (`rem:nonopt`) that
the SOUND channel scheme (keyed by the runtime location `$\ell$`) and the OPTIMAL
scheme (keyed by the interned StateId trace `$tc(K)$`) induce the SAME CLTS; the
in-Rho realization forces this to be proven.

`InRhoSameCLTSWeakBisim` (FV Phase C, obligation iii) discharges it: the `sa:`/`eq:`
steps erase to `$\tau$` (`optimal_visible_equals_sound` — the two schemes' visible
schedules are identical), and the two schemes are weakly bisimilar
(`same_clts_weak_bisim` — the CLTS is independent of the channel scheme). The
bisimulation's forward condition (every sound firing has a complete `sa:` chain) is
discharged by `positions_count` (the O1 symbol-once totality, ii); its backward
condition (distinct `$R_{op}$`-equivalent contexts share, distinct ones get distinct
channels — no cross-talk) by `tc_sound` (the O3 quotient, viii). Non-vacuity is real:
the sound scheme is keyed by LOCATION, so two redexes at different locations share
the optimal channel yet get distinct sound channels — the cross-location sharing is
exactly what is shown invisible. This is the load-bearing `rem:nonopt` discharge —
the previously-asserted claim, now proven zero-admission.
