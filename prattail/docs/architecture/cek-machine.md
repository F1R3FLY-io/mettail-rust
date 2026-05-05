# CEK Machine Architecture

PraTTaIL's parsing pipeline is structurally isomorphic to a **CEK machine** (Felleisen & Friedman, 1986). The original trampoline-era backend implemented this directly with `Frame_Cat` enum continuations and a `'drive` loop in `trampoline.rs`; post-Stage-10 (2026-05-04) the WPDS Walker hosts the same isomorphism via `WpdsState` (Control), the GSS frontier of `RuleAt` / `MixfixMarker` / `OptionalGroupAt` / `BinderRule` symbols (Kontinuation), and the live-builder `WpdsTermBuilder` (Environment). This document formalizes the isomorphism and its consequences.

> **Note**: This document covers the **parsing CEK** machine. The parsing CEK is intentionally
> *not* extended to CESK — parsing is purely functional (no mutable state, no store needed).
> For the **evaluation CESK** machine (with store, GC, mutation), see
> [`cesk-store.md`](cesk-store.md) and [`../design/cesk-machine.md`](../design/cesk-machine.md).

## 1. Component Mapping

| CEK | WPDS Walker (live, post-Stage-10) | Trampoline (historical, Stage 10.6 deleted) |
|-----|-------|----------|
| **C** (Control) | `WpdsState` enum (`PrefixDispatch` / `InfixLoop` / `Unwinding` / `Accepted` / `Error` / `BinderRule` / `OptionalGroup` / `CollectionLoop` / …) at `prattail/src/wpds_runtime.rs` | Token-driven prefix dispatch + binding power (`cur_bp`) + decision tree in `trampoline.rs` (`'drive` loop) |
| **E** (Environment) | `WpdsTermBuilder` live builder + per-cursor argument stacks (`prattail/src/wpds_walker.rs`); `CekEnvironment` (evaluator-side, unchanged) | Accumulated captures in `Frame_Cat` fields in `trampoline.rs` (`SegmentCapture`); `CekEnvironment` in `cek.rs` |
| **K** (Kontinuation) | GSS frontier of `StackSymbolV2` symbols (`RuleAt`, `MixfixMarker`, `GroupingMarker`, `OptionalGroupAt`, `CollectionMarker`) in `prattail/src/wpds_walker.rs` | `Vec<Frame_Cat>` explicit continuation stack with TLS pooling in `trampoline.rs` (`FRAME_POOL_Cat`) |

## 2. Formal Transition Rules

The parser's small-step operational semantics consists of 10 transition rules. We write `⟨C, E, K⟩` for a configuration where `C` is the control state, `E` is the environment (captured values), and `K` is the continuation stack.

### Definition 1: Configurations

A **configuration** is a triple `(phase, locals, stack)` where:

- `phase ∈ { Drive(cat, bp), Prefix(cat, tok, bp), Infix(cat, lhs, bp), Unwind(cat, v), Accept(v), Error(msg) }`
- `locals` is a map from variable names to values (the frame fields)
- `stack` is a sequence of frames `[F₁, F₂, …, Fₙ]`

### Definition 2: Frames

A **frame** is a tagged record:

```
Frame ::= InfixRHS { lhs: Cat, op_pos: ℕ, saved_bp: ℕ }
        | GroupClose { saved_bp: ℕ }
        | UnaryPrefix_L { saved_bp: ℕ }        for each unary prefix label L
        | RD_L_i { saved_bp: ℕ, c₁: T₁, …, cₖ: Tₖ }
                                                 for each RD label L, segment i
        | CollectionElem_L { elements: [Cat], saved_bp: ℕ }
        | Mixfix_L_i { lhs: Cat, saved_bp: ℕ, p₁: T₁, …, pⱼ: Tⱼ }
```

### Definition 3: Transition Rules

| # | Rule | From | To | Stack Op |
|---|------|------|----|----------|
| 1 | DRIVE | `Drive(cat, bp)` | `Prefix(cat, tokens[pos], bp)` | — |
| 2 | PREFIX-TERMINAL (with NT) | `Prefix(cat, tok, bp)` | `Drive(cat, bp')` | push `Frame` |
| 3 | PREFIX-TERMINAL (leaf) | `Prefix(cat, tok, bp)` | `Infix(cat, v, bp)` | — |
| 4 | PREFIX-TAIL (BP02) | `Prefix(cat, tok, bp)` | `Drive(cat, R.bp)` | set tail_wrap |
| 5 | INFIX | `Infix(cat, lhs, bp)` with `l_bp ≥ bp` | `Drive(cat, r_bp)` | push `InfixRHS{lhs, op_pos, bp}` |
| 6 | POSTFIX | `Infix(cat, lhs, bp)` | `Infix(cat, f(lhs), bp)` | — |
| 7 | UNWIND-INFIX | `Unwind(cat, rhs)` | `Infix(cat, f(lhs,rhs), saved_bp)` | pop `InfixRHS` |
| 8 | UNWIND-PREFIX | `Unwind(cat, v)` | `Infix(cat, wrap(v), saved_bp)` | pop `UnaryPrefix` |
| 9 | UNWIND-RD | `Unwind(cat, nt)` | `Drive(cat, bp')` or `Infix(cat, v, bp)` | pop `RD_L_i` |
| 10 | UNWIND-EMPTY | `Unwind(cat, v)` | `Accept(v)` | stack empty |

### Theorem 1 (Determinism)

For any configuration `(phase, locals, stack)` with non-empty remaining input, at most one transition rule applies.

*Proof sketch.* Rules 1–4 are mutually exclusive by phase tag (`Drive` vs `Prefix` vs `Infix` vs `Unwind`). Within `Prefix`, rules 2–4 partition by the presence/kind of same-category nonterminal. Within `Infix`, rules 5–6 partition by operator presence and BP comparison. Within `Unwind`, rules 7–10 partition by frame variant tag. ∎

## 3. CEK ↔ WPDS Correspondence

The WPDS (`wpds.rs`) models the same pushdown automaton at compile time.

### Abstraction Function α

```
α : Configuration → WPDS Configuration
α(phase, locals, stack) = ⟨p, γ₁ γ₂ … γₙ⟩
```

where `p` is the single WPDS control location, and each `γᵢ = StackSymbol::rule_position(cat, label, pos)` is the WPDS stack symbol corresponding to frame `Fᵢ` via the CEK-3 bijection.

### Theorem 2 (Forward Simulation)

For every concrete transition `s → s'`, there exists a WPDS transition sequence `α(s) →*_WPDS α(s')`.

*Proof.* Case analysis on the 10 transition rules. See `formal/rocq/trampoline/theories/WpdsSimulation.v` (the proof remains valid for the WPDS Walker since the Walker IS the WPDS — the simulation is now identity rather than abstraction).

### Corollary (Dead Rule Soundness)

If a WPDS stack symbol has zero weight in the poststar P-automaton, the corresponding frame variant is never pushed during any parse.

## 4. Optimizations Derived from the CEK Model

### CEK-1: Environment Trimming

**Observation.** Frame variant fields are the "E" (environment) component. Many captures are dead at certain segment boundaries — they were captured in segment i but are never referenced by segments i+1, …, n or the constructor.

**Optimization.** Backward liveness analysis over segments eliminates dead captures, reducing frame size.

### CEK-2: Continuation Compression

**Observation.** Consecutive unary prefix operators create a chain of frames, each containing only `saved_bp: u8`.

**Optimization.** Replace `Option<(u8, u8)>` tail_wrap with `Vec<(u8, u8)>` to accumulate the chain and apply all wrappers at once.

### CEK-4: Dead Frame Elimination

**Observation.** WPDS poststar proves certain stack configurations unreachable.

**Optimization.** Via the CEK-3 bijection, suppress codegen for frame variants that correspond to zero-weight WPDS symbols.

### CEK-5: Context-Sensitive FIRST Sets

**Observation.** FIRST sets computed context-free union over all call contexts. Some tokens are only FIRST in certain stack contexts.

**Optimization.** Use poststar P-automaton to restrict FIRST sets by calling context, reducing false ambiguities.

## 5. Defunctionalization

The `Frame_Cat` enum is a **defunctionalization** (Reynolds, 1972) of continuation closures. Each variant represents a closure's tag, and the unwind handler reproduces the closure's body:

```
Frame_Cat::InfixRHS { lhs, op_pos, saved_bp }
  ↔  λ rhs. (make_infix(tokens[op_pos], lhs, rhs), saved_bp)

Frame_Cat::UnaryPrefix_Neg { saved_bp }
  ↔  λ v. (Cat::Neg(Box::new(v)), saved_bp)
```

The correctness of this defunctionalization is proved in `formal/rocq/trampoline/theories/Defunctionalization.v`.

## 7. Concurrency Extension

The single-threaded CEK machine extends to concurrent evaluation through green
threads (`prattail/src/green_thread.rs`) and channels (`prattail/src/channel.rs`).
Each green thread carries its own CEK triple; the scheduler mediates interleaved
execution over a shared channel map.

### Component Mapping

| CEK Component | Green Thread Field | Type | Notes |
|---------------|-------------------|------|-------|
| **C** (Control) | `GreenThread.state` | `CekThreadState` | Current term under evaluation; thread state subsumes phase |
| **E** (Environment) | `GreenThread.environment` | `im::HashMap<String, im::HashMap<String, String>>` | Persistent; O(1) structural-sharing clone on FORK |
| **K** (Kontinuation) | `GreenThread.continuation` | `im::Vector<String>` | Persistent stack; O(log n) push/pop, O(1) clone |

A **process configuration** is a triple `Sigma = (Pi, Gamma, S)` where `Pi` is
the thread pool, `Gamma` is the channel map, and `S` is the scheduler. See
`prattail/docs/theory/green-thread-semantics.md` Definition 3 for the full
formal definition.

### Concurrent Transition Rules

Rules 11--14 extend the 10 single-threaded CEK rules with process-algebraic
primitives from the pi-calculus. Each rule operates on `Sigma = (Pi, Gamma, S)`.

#### Rule 11: FORK

```
                   [C, E, K] in Pi[tid]        C = PPar(P, Q)
----------------------------------------------------------------------
  Pi' = Pi[tid -> Forked({id_P, id_Q})]
        U {id_P -> (id_P, P, E, [])}
        U {id_Q -> (id_Q, Q, E, [])}
  S'.rq = S.rq U {(pri, age_P) -> id_P, (pri, age_Q) -> id_Q}
```

The parent forks into two child threads, each inheriting the environment `E`
via O(1) persistent clone (`im::HashMap::clone`). Both children start with
fresh empty continuation stacks.

#### Rule 12: SEND

```
       [Send(x, v), E, K] in Pi[tid]        Gamma[E(x)] = ch
----------------------------------------------------------------------
  ch.queue' = ch.queue ++ [v]
  Pi' = Pi[tid -> (tid, (), E, K)]
```

Message `v` is enqueued on channel `ch` (lock-free via crossbeam-channel).
The thread continues with unit `()`. If `ch.waiter_count > 0`, the scheduler
wakes suspended threads (Rule S3 in green-thread-semantics.md).

#### Rule 13: RECEIVE

```
       [Recv(x, body), E, K] in Pi[tid]        Gamma[E(x)] = ch
----------------------------------------------------------------------
  Case ch.queue != []:
    v = head(ch.queue),  ch.queue' = tail(ch.queue)
    E' = E[x -> v]
    Pi' = Pi[tid -> (tid, body, E', K)]

  Case ch.queue = []:
    Pi' = Pi[tid -> Suspended({E(x)})]
```

Non-blocking dequeue via `Channel::try_recv()`. On empty channel, the thread
suspends until a SEND arrives. Join patterns (`for (@x <- a; @y <- b) { ... }`)
suspend on the full set `{a, b}` and wake only when all channels have messages.

#### Rule 14: NEW

```
              [New(x, body), E, K] in Pi[tid]
----------------------------------------------------------------------
  id_ch = Gamma.fresh_id()
  Gamma' = Gamma U {id_ch -> Channel::new(id_ch, x, capacity)}
  E' = E[x -> id_ch]
  Pi' = Pi[tid -> (tid, body, E', K)]
```

A fresh channel is allocated with a unique ID (monotonic `AtomicU64`), registered
in the channel map, and bound to `x` in the thread's environment.

### Correspondence to Single-Threaded CEK

Within any single green thread, the 10 standard CEK transition rules (Section 2)
apply unchanged. The concurrency rules 11--14 interact only with the global
`Sigma` configuration, not with the per-thread `(C, E, K)` stepping. This
separation ensures that the CEK ↔ WPDS correspondence (Section 3) and the
defunctionalization (Section 5) remain valid per-thread.

See `prattail/docs/theory/green-thread-semantics.md` for full formal
definitions, correspondence theorems, and Petri net abstraction. See
`prattail/src/channel.rs` for the channel implementation and
`prattail/src/green_thread.rs` for the green thread data structures.

## 8. References

- Felleisen, M. & Friedman, D. P. (1986). *Control operators, the SECD-machine, and the λ-calculus.* Formal Description of Programming Concepts III.
- Reynolds, J. C. (1972). *Definitional interpreters for higher-order programming languages.* ACM Annual Conference.
- Reps, T., Lal, A. & Kidd, N. (2007). *Program analysis using weighted pushdown systems.* FSTTCS.
- Danvy, O. & Nielsen, L. R. (2003). *Defunctionalization at work.* PPDP.
