# Thread-Safety Verification Pipeline Design

## 1. Motivation

PraTTaIL's green thread runtime introduces concurrent semantics: parallel composition (`P | Q`), channel communication, and join patterns. These constructs enable deadlocks, starvation, data races, and name-scope violations that do not exist in sequential parsers. The verification pipeline detects these at compile time via a 6-phase analysis sequence, each phase building on the results of the previous.

### Design Principles

1. **Compile-time only**: All verification runs during `language!` macro expansion. Zero runtime cost.
2. **Sound but not complete**: False positives are acceptable; false negatives are not. If the pipeline says "safe," it is safe.
3. **Incremental**: Each phase can short-circuit if a previous phase already proved safety or detected an error.
4. **Feature-gated**: The entire pipeline is gated on `feature = "green-threads"`.

## 2. Pipeline Overview

```text
┌──────────────────────────────────────────────────────────────────────────┐
│                    Thread-Safety Verification Pipeline                     │
│                                                                          │
│   ChannelsBlockSpec + Grammar Rules                                      │
│         │                                                                │
│         ▼                                                                │
│   ┌──────────────────────────────────────────┐                           │
│   │ Phase 1: Nominal Scope Analysis          │ → GT04 (freshness)        │
│   │ (channel names, new-scoping, aliasing)   │                           │
│   └──────────────┬───────────────────────────┘                           │
│                  │ scope_map: Map<ChannelId, Scope>                      │
│                  ▼                                                        │
│   ┌──────────────────────────────────────────┐                           │
│   │ Phase 2: Register Allocation Analysis    │ → GT03 (ownership)        │
│   │ (data flow, concurrent access detection) │                           │
│   └──────────────┬───────────────────────────┘                           │
│                  │ access_map: Map<ChannelId, Set<ThreadId>>             │
│                  ▼                                                        │
│   ┌──────────────────────────────────────────┐                           │
│   │ Phase 3: Petri Net Safety                │ → GT01 (deadlock)         │
│   │ (deadlock, boundedness, coverability)    │   GT05 (parallelism)      │
│   └──────────────┬───────────────────────────┘                           │
│                  │ petri_net: PetriNet, marking_graph                    │
│                  ▼                                                        │
│   ┌──────────────────────────────────────────┐                           │
│   │ Phase 4: WPDS Stack-Aware Refinement     │ → GT06 (stack depth)     │
│   │ (context-sensitive reachability)          │                           │
│   └──────────────┬───────────────────────────┘                           │
│                  │ refined_reachability: Set<Configuration>              │
│                  ▼                                                        │
│   ┌──────────────────────────────────────────┐                           │
│   │ Phase 5: Buchi Liveness                  │ → GT02 (starvation)      │
│   │ (starvation, progress, fairness)         │                           │
│   └──────────────┬───────────────────────────┘                           │
│                  │ liveness_result: LivenessVerdict                      │
│                  ▼                                                        │
│   ┌──────────────────────────────────────────┐                           │
│   │ Phase 6: KAT Program Equivalence         │                           │
│   │ (optimization soundness verification)    │                           │
│   └──────────────────────────────────────────┘                           │
│                                                                          │
│   Output: Vec<LintDiagnostic> (GT01-GT06)                                │
└──────────────────────────────────────────────────────────────────────────┘
```

### Phase Dependencies

```text
Phase 1 (Nominal Scope)
    │
    └──→ Phase 2 (Register Allocation) ← uses scope_map
              │
              └──→ Phase 3 (Petri Net) ← uses access_map to refine transitions
                        │
                        └──→ Phase 4 (WPDS) ← uses Petri net marking graph
                                  │
                                  └──→ Phase 5 (Buchi) ← uses WPDS configurations
                                            │
                                            └──→ Phase 6 (KAT) ← uses all prior results
```

## 3. Phase 1: Nominal Scope Analysis

### Purpose

Detect channel freshness violations: when a channel created with `new` (private scope) escapes to an outer scope via aliasing, return values, or captures.

### Formal Model

**Definition 1 (Nominal Automaton)**. A nominal automaton is a tuple `(Q, Σ, δ, q₀, F, R)` where:
- `Q` is a finite set of states.
- `Σ` is an alphabet of channel operations (`new`, `send`, `recv`, `alias`).
- `δ: Q × Σ → Q` is the transition function.
- `q₀ ∈ Q` is the initial state.
- `F ⊆ Q` is the set of accepting (safe) states.
- `R ⊆ ℕ` is a finite set of **registers** holding channel names.

The registers model the pi-calculus restriction operator `(νx)P`: register `r` holds the fresh name `x`, and any transition that reads `r` into an unrestricted context is a freshness violation.

### Algorithm

1. For each `new ch in { ... }` in the grammar, create a register holding `ch.id`.
2. Trace all grammar rules that reference `ch`:
   - Direct use in send/receive: safe (within scope).
   - Capture in a closure that escapes: violation.
   - Return as a value: violation.
   - Alias to another name: violation.
3. Emit GT04 for each detected violation.

### Complexity

O(|channels| * |rules|) — linear scan of rules for each channel.

### Connection to ARA

The register allocation analysis in `ara.rs` (Affine-Relation Analysis) provides the matrix representation. Channel registers are modeled as program variables; an affine relation `ch_new = ch_outer + 0` indicates aliasing.

### Output

```
scope_map: Map<ChannelId, ChannelScope>
```

where `ChannelScope = { Private(rule_range), Public, Escaped(via_rule) }`.

### Lint: GT04

- **Code**: `GT04`
- **Name**: `channel-freshness-violation`
- **Severity**: Warning
- **Message**: "Channel `{channel}` created with `new` escapes via rule `{rule}` in `{grammar_name}`"
- **Hint**: "Restrict channel scope or use explicit export"

## 4. Phase 2: Register Allocation Analysis

### Purpose

Detect data ownership violations: when multiple green threads access the same channel's buffer concurrently without synchronization.

### Formal Model

**Definition 2 (Register Automaton for Ownership)**. Each channel buffer is modeled as a register. A register automaton tracks which threads hold a reference to which registers:

```
access_map: Map<ChannelId, Set<GreenThreadId>>
```

If `|access_map[ch]| > 1` and the operations are not synchronized (i.e., not mediated by the channel's own send/recv protocol), there is a potential data race.

### Algorithm

1. From the grammar's fork points, enumerate all green thread lineages.
2. For each thread, collect the set of channels it accesses.
3. For each channel, compute the set of threads that access it.
4. Flag any channel where multiple threads perform non-channel-mediated access.

**Note**: Channel send/receive operations are safe by construction (crossbeam is thread-safe). Violations arise when threads share channel references and bypass the channel protocol.

### Connection to Phase 1

Phase 2 uses the `scope_map` from Phase 1 to distinguish:
- **Private channels** (created with `new`): Only visible within the `new` block's thread and its children. If Phase 1 found no escape, concurrent access is impossible.
- **Public channels**: May be accessed by any thread; require full analysis.

### Complexity

O(|threads| * |channels|).

### Output

```
access_map: Map<ChannelId, Set<GreenThreadId>>
violations: Vec<(ChannelId, Set<GreenThreadId>)>
```

### Lint: GT03

- **Code**: `GT03`
- **Name**: `data-ownership-violation`
- **Severity**: Error
- **Message**: "Channel `{channel}` accessed concurrently by threads [{threads}] without synchronization in `{grammar_name}`"
- **Hint**: "Use `new` to create a private channel or introduce a mutex pattern"

## 5. Phase 3: Petri Net Safety

### Purpose

Detect deadlocks (circular waits), verify boundedness (finite channel buffers), and count independent parallel regions.

### Formal Model

**Definition 3 (Grammar Petri Net)**. Given a `ChannelsBlockSpec` with channels `C₁, …, Cₖ` and grammar rules containing parallel compositions, construct a Petri net `(P, T, F, W, M₀)` where:

- **Places** `P = P_ch ∪ P_thread`:
  - `P_ch = {p_c | c ∈ channels}` — one place per channel (tokens = buffered messages).
  - `P_thread = {p_t | t ∈ fork_points}` — one place per thread (token = thread is active).
- **Transitions** `T = T_send ∪ T_recv ∪ T_fork ∪ T_join`:
  - `T_send = {t_send(c) | c ∈ channels}` — adds a token to `p_c`.
  - `T_recv = {t_recv(c) | c ∈ channels}` — removes a token from `p_c`.
  - `T_fork = {t_fork(parent, child₁, child₂)}` — removes token from parent, adds to children.
  - `T_join = {t_join(c₁, …, cₙ)}` — multi-input for join patterns.
- **Flow** `F`: Arcs connecting transitions to their input/output places.
- **Weight** `W`: All arcs have weight 1 (unit Petri net).
- **Initial marking** `M₀`: One token in the root thread place; zero tokens in all channel places.

### Deadlock Detection

**Definition 4 (Deadlock)**. A marking `M` is a deadlock if:
1. No transition in `T` is enabled at `M` (no transition has all input places with sufficient tokens).
2. There exists at least one active thread place with a token.

Compute the reachability graph from `M₀` and check for deadlock markings.

### Boundedness

**Definition 5 (k-Boundedness)**. A Petri net is k-bounded if for all reachable markings `M` and all places `p`: `M(p) ≤ k`. Use the Karp-Miller coverability tree to determine boundedness.

For bounded channels (`ChannelCapacity::Bounded(κ)`), verify that the channel place never exceeds κ tokens.

### Independent Parallel Regions

Count the number of connected components in the Petri net's transition relation graph. Each component represents an independent parallel region that can be scheduled without interference.

### Complexity

Reachability graph: O(2^|P|) worst case, but practical for small channel/thread counts. Coverability (Karp-Miller): EXPSPACE in theory, fast in practice for bounded nets.

### Output

```
deadlock_markings: Vec<(Vec<blocked_threads>, Vec<empty_channels>)>
boundedness: Map<PlaceId, Option<usize>>
independent_regions: usize
max_concurrent: usize
```

### Lints: GT01, GT05

**GT01**:
- **Code**: `GT01`
- **Name**: `deadlock-detected`
- **Severity**: Error
- **Message**: "Deadlock detected in `{grammar_name}`: threads [{blocked}] are blocked on empty channels [{empty}]"
- **Hint**: "Ensure at least one active thread can send to {empty}"

**GT05**:
- **Code**: `GT05`
- **Name**: `parallelism-report`
- **Severity**: Note
- **Message**: "{N} independent parallel region(s) detected; max {M} concurrent green threads"
- **Hint**: None

## 6. Phase 4: WPDS Stack-Aware Refinement

### Purpose

Refine the Petri net's reachability analysis with context-sensitive (stack-aware) information. The Petri net is a flat model; the WPDS adds the pushdown stack (continuation stack of each green thread) for more precise analysis.

### Formal Model

**Definition 6 (Concurrent WPDS)**. For each green thread, construct a WPDS modeling the thread's CEK transitions. The product of all per-thread WPDSs, synchronized on channel operations, is the concurrent WPDS.

Each WPDS rule corresponds to a CEK transition:

| CEK Transition | WPDS Rule | Stack Effect |
|----------------|-----------|--------------|
| DRIVE | `⟨p, γ_drive⟩ → ⟨p, γ_prefix⟩` | replace |
| PREFIX (with NT) | `⟨p, γ_prefix⟩ → ⟨p, γ_frame γ_drive⟩` | push |
| INFIX | `⟨p, γ_infix⟩ → ⟨p, γ_rhs γ_drive⟩` | push |
| UNWIND | `⟨p, γ_unwind⟩ → ⟨p, ε⟩` | pop |
| SEND | `⟨p, γ_send⟩ → ⟨p, γ_continue⟩` | replace (sync) |
| RECV | `⟨p, γ_recv⟩ → ⟨p, γ_continue⟩` | replace (sync) |

### Poststar Analysis

Run `poststar()` on the concurrent WPDS to compute the set of all reachable stack configurations. Use these to:

1. **Confirm Petri net deadlocks**: If the WPDS poststar shows a deadlock marking is unreachable in context, demote GT01 from Error to Note.
2. **Compute stack depth bounds**: For each category, the maximum stack depth in the poststar P-automaton gives an upper bound.
3. **Context-sensitive FIRST sets**: Restrict channel operation reachability by stack context.

### Complexity

Poststar on a WPDS with `n` rules and `k` stack symbols: O(n * k^2) for the saturated P-automaton.

### Output

```
refined_reachability: Set<ConcurrentConfiguration>
stack_depth_bounds: Map<String, usize>    // category → max depth
```

### Lint: GT06

- **Code**: `GT06`
- **Name**: `stack-depth-estimate`
- **Severity**: Note
- **Message**: "Category `{category}` in `{grammar_name}`: WPDS estimates max stack depth {depth}"
- **Hint**: "Preallocate continuation stack to {depth}"

## 7. Phase 5: Buchi Liveness

### Purpose

Detect starvation: infinite executions where some green thread never makes progress.

### Formal Model

**Definition 7 (Progress Property)**. For each green thread `t`, define the LTL formula:

```
progress_t = GF(t transitions)
```

i.e., "globally, finitely often, thread `t` takes a transition." This is a standard fairness property.

**Definition 8 (Starvation)**. Thread `t` starves if there exists an infinite execution `π` such that `π ⊭ GF(t transitions)`.

### Algorithm

1. Construct a Buchi automaton `B_¬progress` for the negation of the progress property: `¬GF(t transitions) = FG(¬(t transitions))`.
2. Construct the system automaton `S` from the WPDS configurations (Phase 4).
3. Compute the product `S × B_¬progress`.
4. Check emptiness of the product. If non-empty, a witness infinite execution demonstrating starvation exists.

The product construction uses `WeightedBuchiAutomaton::intersect()` from `buchi.rs`. Emptiness is checked via nested DFS (Tarjan's algorithm on the product graph).

### Connection to Phase 4

Phase 5 uses the `refined_reachability` from Phase 4 to construct the system automaton. This avoids false positives from infeasible stack configurations.

### Complexity

Product construction: O(|S| * |B|). Emptiness: O(|S| * |B|) via nested DFS.

### Output

```
starving_threads: Vec<String>
liveness_verdict: LivenessVerdict { safe: bool, witnesses: Vec<WitnessTrace> }
```

### Lint: GT02

- **Code**: `GT02`
- **Name**: `potential-starvation`
- **Severity**: Warning
- **Message**: "Thread `{thread_name}` may starve in `{grammar_name}`: Buchi analysis found infinite execution without progress"
- **Hint**: "Add fairness constraint or reduce priority inversion"

## 8. Phase 6: KAT Program Equivalence

### Purpose

Verify that grammar transformations and optimizations preserve the concurrent behavior of the program.

### Formal Model

**Definition 9 (KAT Equivalence)**. Given two KAT expressions `e₁` (original) and `e₂` (optimized), they are equivalent iff they denote the same set of guarded strings: `⟦e₁⟧ = ⟦e₂⟧`.

**Definition 10 (Hoare Triple in KAT)**. The Hoare triple `{b} p {c}` is valid iff `b · p · c̄ = 0` in the free KAT. This encodes: "if precondition `b` holds and program `p` executes, then postcondition `c` holds."

### Algorithm

1. Encode the grammar's channel flow as a KAT expression:
   - Sequential composition (`·`): rule chaining.
   - Alternation (`+`): dispatch.
   - Iteration (`*`): recursive categories.
   - Boolean tests (`b`): channel readiness, thread state predicates.
2. For each optimization, encode the transformed flow as `e₂`.
3. Check `e₁ = e₂` via `check_equivalence()` from `kat.rs`.

### Connection to Prior Phases

Phase 6 uses all prior results to construct accurate KAT models:
- Phase 1 scope → test atoms (`channel_private(ch)`).
- Phase 3 Petri net → test atoms (`deadlock_free`).
- Phase 4 WPDS → action terms with stack context.
- Phase 5 Buchi → test atoms (`starvation_free`).

### Complexity

KAT equivalence is decidable in PSPACE via automata-based bisimulation (Kozen & Smith, 1996). In practice, the symbolic algorithms of Pous (2015) are efficient for the small KAT expressions generated from grammar flows.

### Output

```
equivalences: Vec<(KatExpr, KatExpr, bool)>
hoare_triples: Vec<(BooleanTest, KatExpr, BooleanTest, bool)>
```

## 9. Pipeline Orchestration

### Short-Circuit

The pipeline short-circuits on fatal errors:
- If Phase 3 detects a deadlock (GT01 Error), Phases 4-6 still run but their results are advisory.
- If Phase 2 detects a data race (GT03 Error), the grammar is unsound; all subsequent phases note this.

### Incremental

When the grammar is modified, only phases whose inputs changed are re-run:
- Modifying a channel declaration invalidates Phases 1-6.
- Modifying a grammar rule (non-channel) invalidates Phases 3-6.
- Modifying a fork point invalidates Phases 3-6.

### Cost-Benefit

The pipeline is controlled by the `GT01:GreenThreadForkJoin` optimization gate in `cost_benefit.rs`:

| Property | Value |
|----------|-------|
| **Speedup** | 0.35 |
| **Cost** | 0.25 |
| **Applicability** | `category_count >= 2` |

If the cost-benefit analysis determines the grammar is too simple (single category), the pipeline is skipped entirely.

### Feature Gate

All verification phases require `feature = "green-threads"`:

```rust
#[cfg(feature = "green-threads")]
pub fn verify_thread_safety(
    channels: &ChannelsBlockSpec,
    grammar: &GrammarSpec,
) -> Vec<LintDiagnostic> { ... }
```

The `green-threads` feature transitively enables:
- `cek-runtime` (CEK observer infrastructure)
- `dep:im` (persistent data structures)
- `dep:crossbeam-channel` (lock-free MPMC channels)
- `dep:dashmap` (lock-free concurrent maps)
- `dep:num_cpus` (core count detection)

And for verification, the following features must also be enabled:
- `petri` (Petri net analysis)
- `omega` (Buchi automata)
- `kat` (Kleene Algebra with Tests)
- `ltl` (LTL model checking)

## 10. Files Modified

| File | Change |
|------|--------|
| `prattail/src/channel.rs` | Channel types, ChannelMap, JoinPatternSpec, ChannelWaiter |
| `prattail/src/green_thread.rs` | GreenThread, CekThreadState, GreenThreadRegistry |
| `prattail/src/scheduler.rs` | Scheduler FSM, SchedulerMetrics |
| `prattail/src/global_pool.rs` | GlobalPool singleton, HillClimber, AnyScheduler |
| `prattail/src/petri.rs` | `construct_petri_net()`, `check_deadlock()`, `check_boundedness()` |
| `prattail/src/buchi.rs` | `WeightedBuchiAutomaton::intersect()`, `check_emptiness()` |
| `prattail/src/kat.rs` | `check_equivalence()`, `verify_hoare_triple()` |
| `prattail/src/verify.rs` | `check_safety()`, `build_bad_state_automaton()` |
| `prattail/src/wpds.rs` | Poststar for concurrent WPDS |
| `prattail/src/ara.rs` | Register allocation for channel ownership analysis |
| `prattail/src/lint.rs` | GT01-GT06 lint functions |
| `prattail/src/cost_benefit.rs` | `Optimization::GreenThreadForkJoin` gate |
| `prattail/src/lib.rs` | Feature-gated module declarations |

## 11. Lints (Full Descriptions)

### GT01: deadlock-detected

| Property | Value |
|----------|-------|
| **Code** | `GT01` |
| **Name** | `deadlock-detected` |
| **Severity** | Error |
| **Phase** | 3 (Petri Net Safety) |
| **Feature gate** | `green-threads` |
| **Implementation** | `lint.rs:lint_gt01_deadlock()` |

**Detection**: Construct a Petri net from the `channels {}` block. Compute the reachability graph from the initial marking. If any reachable marking has no enabled transition AND at least one active thread place has a token, report deadlock.

**Message**: "Deadlock detected in `{grammar_name}`: threads [{blocked_threads}] are blocked on empty channels [{empty_channels}]"

**Hint**: "Ensure at least one active thread can send to {empty_channels}"

**Example trigger**:
```
channels {
    a: Channel<i32>;
    b: Channel<i32>;
}
// Thread 1: recv a, send b
// Thread 2: recv b, send a
// → Circular wait deadlock
```

### GT02: potential-starvation

| Property | Value |
|----------|-------|
| **Code** | `GT02` |
| **Name** | `potential-starvation` |
| **Severity** | Warning |
| **Phase** | 5 (Buchi Liveness) |
| **Feature gate** | `green-threads` |
| **Implementation** | `lint.rs:lint_gt02_starvation()` |

**Detection**: Construct a Buchi automaton for `¬GF(thread_i progresses)`. Intersect with the system automaton (from WPDS configurations). If the product is non-empty, thread_i may starve.

**Message**: "Thread `{thread_name}` may starve in `{grammar_name}`: Buchi analysis found infinite execution without progress"

**Hint**: "Add fairness constraint or reduce priority inversion"

### GT03: data-ownership-violation

| Property | Value |
|----------|-------|
| **Code** | `GT03` |
| **Name** | `data-ownership-violation` |
| **Severity** | Error |
| **Phase** | 2 (Register Allocation Analysis) |
| **Feature gate** | `green-threads` |
| **Implementation** | `lint.rs:lint_gt03_ownership()` |

**Detection**: From the register automaton, compute the set of threads accessing each channel. If `|threads| > 1` and the access is not mediated by the channel's send/recv protocol, report violation.

**Message**: "Channel `{channel}` accessed concurrently by threads [{threads}] without synchronization in `{grammar_name}`"

**Hint**: "Use `new` to create a private channel or introduce a mutex pattern"

### GT04: channel-freshness-violation

| Property | Value |
|----------|-------|
| **Code** | `GT04` |
| **Name** | `channel-freshness-violation` |
| **Severity** | Warning |
| **Phase** | 1 (Nominal Scope Analysis) |
| **Feature gate** | `green-threads` |
| **Implementation** | `lint.rs:lint_gt04_freshness()` |

**Detection**: For each channel created with `new`, trace all references. If a reference escapes the `new` block's scope (via aliasing, return, or capture), report violation.

**Message**: "Channel `{channel}` created with `new` escapes via rule `{rule}` in `{grammar_name}`"

**Hint**: "Restrict channel scope or use explicit export"

### GT05: parallelism-report

| Property | Value |
|----------|-------|
| **Code** | `GT05` |
| **Name** | `parallelism-report` |
| **Severity** | Note |
| **Phase** | 3 (Petri Net Safety) |
| **Feature gate** | `green-threads` |
| **Implementation** | `lint.rs:lint_gt05_parallelism()` |

**Detection**: Count connected components in the Petri net transition relation graph. Each component is an independent parallel region.

**Message**: "{N} independent parallel region(s) detected; max {M} concurrent green threads"

**Hint**: None

### GT06: stack-depth-estimate

| Property | Value |
|----------|-------|
| **Code** | `GT06` |
| **Name** | `stack-depth-estimate` |
| **Severity** | Note |
| **Phase** | 4 (WPDS Stack-Aware Refinement) |
| **Feature gate** | `green-threads` |
| **Implementation** | `lint.rs:lint_gt06_stack_depth()` |

**Detection**: From the poststar P-automaton, compute the longest accepting path for each category's stack symbol. This is an upper bound on the continuation stack depth.

**Message**: "Category `{category}` in `{grammar_name}`: WPDS estimates max stack depth {depth}"

**Hint**: "Preallocate continuation stack to {depth}"

## 12. Worked Example

### Grammar

```
language! {
    name = "ConcurrentCalc";
    channels {
        results: Channel<i32>;
    }
    Expr {
        Add . left:Expr "+" right:Expr → Expr::Add(left, right)
        Par . "(" left:Expr "|" right:Expr ")" → Expr::Par(left, right)
        Num . n:Int → Expr::Num(n)
    }
    Int {
        N . /[0-9]+/ → Int::N(token)
    }
}
```

### Phase 1: Nominal Scope Analysis

Channel `results` is declared at the top level (not inside `new`), so it is public. No freshness violations.

```
scope_map = { results → Public }
GT04: (no violations)
```

### Phase 2: Register Allocation Analysis

The `Par` rule forks two green threads. Both threads may access `results`:

```
access_map = { results → { gt#0 (left), gt#1 (right) } }
```

Since `results` is a `Channel` (crossbeam, lock-free MPMC), concurrent send/recv is safe by construction. No ownership violations.

```
GT03: (no violations)
```

### Phase 3: Petri Net Safety

```text
Places:
  p_results (channel buffer)
  p_root (root thread)
  p_left (left fork)
  p_right (right fork)

Transitions:
  t_fork: p_root → p_left + p_right
  t_send_left: p_left → p_results + p_left_done
  t_send_right: p_right → p_results + p_right_done

Initial marking: M₀ = {p_root: 1, others: 0}
```

Reachability graph shows no deadlock markings (all threads can proceed independently).

```
GT01: (no deadlocks)
GT05: 2 independent parallel regions; max 2 concurrent green threads
```

### Phase 4: WPDS Stack-Aware Refinement

```
Stack depth bounds:
  Expr: max 3 (recursive Add)
  Int: max 1

GT06: Category "Expr": WPDS estimates max stack depth 3
GT06: Category "Int": WPDS estimates max stack depth 1
```

### Phase 5: Buchi Liveness

Both `gt#0` (left) and `gt#1` (right) always terminate (no receive operations that could block indefinitely). The Buchi product is empty for both threads.

```
GT02: (no starvation)
```

### Phase 6: KAT Program Equivalence

The `Par` rule's fork/join is equivalent to sequential evaluation when the two branches do not communicate:

```
KAT: left · right = left + right (commutativity of independent actions)
Hoare triple: {channel_empty(results)} Par {channel_has(results, 2)}
→ Valid
```

### Final Diagnostics

```
note[GT05]: 2 independent parallel region(s) detected; max 2 concurrent green threads
note[GT06]: Category "Expr" in "ConcurrentCalc": WPDS estimates max stack depth 3
note[GT06]: Category "Int" in "ConcurrentCalc": WPDS estimates max stack depth 1
```

No errors or warnings — the grammar is provably thread-safe.

## 13. References

- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus*. Cambridge University Press.
- Petri, C. A. (1962). *Kommunikation mit Automaten*. Ph.D. thesis, University of Bonn.
- Karp, R. M. & Miller, R. E. (1969). Parallel program schemata. *JCSS*, 3(2):147-195.
- Esparza, J. & Nielsen, M. (1994). Decidability issues for Petri nets. *BRICS Report Series*, RS-94-8.
- Reps, T., Lal, A. & Kidd, N. (2007). Program analysis using weighted pushdown systems. *FSTTCS*.
- Schwoon, S. (2002). *Model-Checking Pushdown Systems*. Ph.D. thesis, TU Munich.
- Vardi, M. Y. & Wolper, P. (1994). Reasoning about infinite computations. *Information and Computation*, 115(1):1-37.
- Buchi, J. R. (1962). On a decision method in restricted second order arithmetic. *Proceedings of the International Congress on Logic, Methodology and Philosophy of Science*, pp. 1-11.
- Kozen, D. (1997). Kleene algebra with tests. *ACM TOPLAS*, 19(3):427-443.
- Kozen, D. & Smith, F. (1996). Kleene algebra with tests: completeness and decidability. *Proceedings of CSL*, LNCS 1258.
- Pous, D. (2015). Symbolic algorithms for language equivalence and Kleene algebra with tests. *Proceedings of POPL*.
- Kaminski, M. & Francez, N. (1994). Finite-memory automata. *TCS*, 134(2):329-363.
