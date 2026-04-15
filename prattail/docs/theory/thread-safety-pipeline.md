# Thread Safety Verification Pipeline

This document formalizes the 6-phase static analysis pipeline that verifies
thread-safety properties of PraTTaIL green thread programs at compile time.
Each phase applies a progressively more precise abstraction, forming a
**precision lattice** from lightweight syntactic checks to full temporal
verification.

**Source files**: `prattail/src/green_thread.rs`, `prattail/src/channel.rs`,
`prattail/src/scheduler.rs`, `prattail/src/wpds.rs`, `prattail/src/buchi.rs`,
`prattail/src/kat.rs`, `prattail/src/pipeline.rs`, `prattail/src/lint.rs`.

**Feature gate**: Phases 1--3 require `green-threads`. Phase 4 requires `green-threads`.
Phase 5 requires `green-threads` + `buchi`. Phase 6 requires `green-threads` + `kat`.

---

## 1. Precision Lattice

The 6 phases form a total order by precision, where each subsequent phase
subsumes and refines the previous:

```
Phase 1        Phase 2        Phase 3        Phase 4        Phase 5        Phase 6
Nominal    ⊑   Register   ⊑   Petri Net  ⊑   WPDS       ⊑   Buchi×WPDS ⊑   KAT
Automata       Automata       Coverability    Reachability    Liveness       Equivalence
  │              │              │               │               │              │
  ▼              ▼              ▼               ▼               ▼              ▼
Syntactic     Data-dep      Boundedness    Context-sens    Temporal        Program
name check    tracking      + deadlock     reachability    properties      equivalence
              (register)    detection      (pushdown)      (omega)         (algebra)
```

### Definition 1 (Precision Lattice)

The **precision lattice** `(L, ⊑)` is the total order:

```
L = { Nominal, Register, PetriNet, WPDS, BuchiWPDS, KAT }

Nominal ⊑ Register ⊑ PetriNet ⊑ WPDS ⊑ BuchiWPDS ⊑ KAT
```

where `A ⊑ B` means that every property provable at level `A` is also provable
at level `B`, and `B` may prove strictly more properties than `A`.

### Soundness Guarantee

Every phase in the pipeline is **sound**: if a phase reports "safe," then the
property holds in all concrete executions. Phases may be **incomplete** (report
"unknown" or "potentially unsafe" for programs that are actually safe).

### Phase Selection Heuristic

The pipeline runs phases in order, early-terminating when a phase proves all
required properties. For small grammars (< 10 categories, < 5 channels), Phase 1
is typically sufficient. Grammars with join patterns or recursive channel creation
may require Phase 3 or higher.

---

## 2. Phase 1: Nominal Automata Theory

**Based on**: Bojańczyk, Klin & Lasota (2014). *Automata theory in nominal sets.*

### Definition 2 (Nominal Channel Automaton)

A **nominal channel automaton** `A_N = (Q, Σ_N, δ_N, q₀, F)` where:

- `Q = { q_idle, q_sending, q_receiving, q_joined, q_closed }` is the finite set
  of channel states.
- `Σ_N = Names × Ops` where `Names` is the set of channel names from the
  grammar's `channels {}` block (`ChannelSpec.name`) and
  `Ops = { create, send, recv, close, join }`.
- `δ_N : Q × Σ_N → Q` is the transition function.
- `q₀ = q_idle`.
- `F = { q_idle, q_closed }` (accepting = safe terminal states).

### Transition Table

| From | Action | To | Condition |
|------|--------|----|-----------|
| `q_idle` | `create(ch)` | `q_idle` | `ch` fresh in scope |
| `q_idle` | `send(ch, v)` | `q_sending` | `ch` exists |
| `q_sending` | `send(ch, v)` | `q_sending` | -- |
| `q_idle` | `recv(ch)` | `q_receiving` | `ch` exists |
| `q_receiving` | `recv(ch)` | `q_receiving` | -- |
| `q_receiving` | `join(ch₁, ..., chₖ)` | `q_joined` | all `chᵢ` exist |
| `q_idle` | `close(ch)` | `q_closed` | `ch` exists |
| `q_sending` | `close(ch)` | `q_closed` | -- |

### Properties Checked

- **GT01 (Undefined Channel)**: Every `send(ch)` and `recv(ch)` references a
  channel name that appears in the `channels {}` block or was created by a
  `NEW` operation in scope.
- **GT02 (Send After Close)**: No `send(ch)` occurs after `close(ch)` on the
  same channel.

### Theorem 6 (Nominal Phase Soundness)

If the nominal automaton `A_N` accepts the sequence of channel operations
extracted from the grammar AST, then properties GT01 and GT02 hold for all
concrete executions.

**Proof.** The nominal automaton tracks channel names syntactically. Each channel
operation is mapped to a transition; rejected sequences correspond to undefined
channel references (GT01) or protocol violations (GT02). Since the automaton is
deterministic and the operation sequence is extracted conservatively (over-
approximating all possible interleavings by ignoring thread identity), acceptance
implies safety. ∎

---

## 3. Phase 2: Register Automata Theory

**Based on**: Kaminski & Francez (1994). *Finite-memory automata.*

### Definition 3 (Channel Register Automaton)

A **channel register automaton** `A_R = (Q, R, Σ_R, δ_R, q₀, F)` where:

- `Q` is a finite set of control states (augmenting Phase 1 with data tracking).
- `R = {r₁, r₂, ..., rₖ}` is a finite set of registers, one per channel,
  storing the `ChannelId` assigned at creation time.
- `Σ_R = Ops × RegisterRef` where operations reference registers (not bare names).
- `δ_R : Q × R^k × Σ_R → Q × R^k` is the transition function with register
  updates.
- `q₀` is the initial state with all registers empty (`⊥`).
- `F` is the set of accepting states.

### Properties Checked (beyond Phase 1)

- **GT03 (Channel Aliasing)**: Detects when two distinct names are bound to the
  same `ChannelId` (via assignment), which may cause unexpected sharing.
- **GT04 (Register Overflow)**: The number of simultaneously live channels does
  not exceed the register count `k` (configurable; default = number of channels
  declared in the `channels {}` block).

### Theorem 7 (Register Phase Soundness)

If the register automaton `A_R` accepts the operation sequence with register
assignments, then properties GT01--GT04 hold.

**Proof.** The register automaton extends Phase 1 by tracking identity (not just
names). Each `NEW` operation stores a fresh ID in a register; each `SEND` /
`RECV` operation compares the referenced register to the target register.
Aliasing (GT03) is detected when two registers hold the same value. Overflow
(GT04) is detected when all registers are occupied and a `NEW` is attempted.
Since registers faithfully track the `AtomicU64` ID allocation in
`ChannelMap::fresh_id()`, and the automaton over-approximates all interleavings,
acceptance implies safety. ∎

---

## 4. Phase 3: Petri Net Theory

**Based on**: Karp & Miller (1969). *Parallel program schemata.*

### Definition 4 (Process Petri Net)

The **process Petri net** `N = (P, T, F, M₀)` is constructed from the grammar's
concurrency structure as defined in Definition 4 of
`green-thread-semantics.md`, Section 4.

### Properties Checked (beyond Phase 2)

- **Boundedness (GT05)**: For every channel place `p_ch`, there exists a bound
  `B ∈ ℕ` such that `M(p_ch) ≤ B` in all reachable markings. Unbounded channels
  may lead to memory exhaustion.
- **Deadlock Detection**: No reachable marking has all thread places empty
  (all threads terminated or suspended) while channel places are non-empty
  (undelivered messages).
- **Mutual Exclusion**: Critical sections guarded by channels enforce at most
  one thread in the section at any time.

### Karp-Miller Tree Construction

The coverability tree is constructed by:

1. Starting from initial marking `M₀` (one token in the root thread place).
2. For each enabled transition, compute the successor marking.
3. If a marking `M'` dominates an ancestor `M` (i.e., `M' ≥ M` componentwise
   and `M' ≠ M`), replace the strictly greater components with `ω` (unbounded).
4. Terminate when no new markings can be discovered.

### Theorem 8 (Petri Net Boundedness Decidability)

The boundedness problem for the process Petri net is decidable via the
Karp-Miller coverability tree, with complexity at most `O(2^{2^n})` where
`n = |P|` is the number of places. For typical grammars with `|P| < 20`, this
is feasible.

**Proof.** By Karp & Miller (1969, Theorem 1). The coverability tree is finite
and its construction terminates. A place is bounded iff its `ω`-free value in
the tree is finite across all leaves. ∎

### Theorem 9 (Deadlock Detection Soundness)

If the Karp-Miller tree contains no leaf marking where all thread places are 0
and at least one channel place is non-zero, then the grammar is deadlock-free
under cooperative scheduling.

**Proof.** The Karp-Miller tree covers all reachable markings. A deadlock
corresponds to a marking where no transition is enabled: all thread places are
empty (or suspended) while messages remain undelivered. If no such marking
appears in the coverability tree, it is unreachable. Since the Petri net
over-approximates the concrete semantics (Theorem 4 of
`green-thread-semantics.md`), absence in the Petri net implies absence in the
concrete system. ∎

---

## 5. Phase 4: WPDS Theory

**Based on**: Reps, Lal & Kidd (2007). *Program analysis using weighted pushdown systems.*

### Definition 5 (Thread WPDS)

The **thread WPDS** extends the parser WPDS (`prattail/src/wpds.rs`) with stack
symbols for concurrency operations:

```
Γ_thread = Γ_parser ∪ { Fork(cat₁, cat₂), Send(ch), Recv(ch), New(ch) }
```

WPDS rules for concurrency:

| Rule Type | Pattern | Weight |
|-----------|---------|--------|
| Fork | `⟨p, Fork(c₁,c₂)⟩ → ⟨p, c₁⟩` | `w_fork` |
| Send | `⟨p, Send(ch)⟩ → ⟨p, ε⟩` | `w_send(ch)` |
| Recv | `⟨p, Recv(ch)⟩ → ⟨p, ε⟩` | `w_recv(ch)` |
| New | `⟨p, New(ch)⟩ → ⟨p, ε⟩` | `w_new` |

### Properties Checked (beyond Phase 3)

- **Context-sensitive reachability**: Which (thread state, stack configuration)
  pairs are reachable? Uses poststar computation on the product P-automaton.
- **Interprocedural channel flow**: Track which channels are reachable from
  which thread contexts, accounting for the pushdown stack structure.
- **Dead thread detection**: A thread whose stack configuration has zero weight
  in the poststar P-automaton is unreachable (analogous to dead rule detection
  in the parser WPDS).

### Theorem 10 (WPDS Reachability Soundness)

If a thread stack configuration `⟨p, γ₁γ₂...γₙ⟩` has zero weight in the
poststar P-automaton, then no concrete execution reaches that configuration.

**Proof.** By the fundamental theorem of WPDS reachability analysis (Reps et al.,
2007, Theorem 3). The poststar computation computes the least fixed point of
the WPDS transition system over the weight domain. Zero weight in the
P-automaton corresponds to an unreachable configuration in the weighted
transition system. Since the WPDS over-approximates the concrete green thread
semantics (Theorem 5 of `green-thread-semantics.md`), unreachability in the
WPDS implies unreachability in the concrete system. ∎

---

## 6. Phase 5: Buchi x WPDS Product Theory

**Based on**: Esparza, Hansel, Rossmanith & Schwoon (2000). *Efficient algorithms
for model checking pushdown systems.*

### Definition 6 (Buchi x WPDS Product)

The **Buchi x WPDS product** `P = B × W` is the product of:

- `B = (Q_B, Σ_B, δ_B, q₀_B, F_B)` -- a Buchi automaton specifying a liveness
  property (e.g., "every SEND is eventually followed by a RECV on the same
  channel").
- `W = (P_W, Γ_W, Δ_W)` -- the thread WPDS from Phase 4.

The product automaton `P` has control states `Q_B × P_W`, stack alphabet `Γ_W`,
and accepts infinite runs where the Buchi acceptance condition is satisfied
infinitely often along the WPDS execution.

### Properties Checked (beyond Phase 4)

- **Liveness (GT06)**: Every message sent on a channel is eventually received
  (no permanent message starvation under fair scheduling).
- **Starvation freedom**: Every `Ready` thread is eventually `Running`.
- **Response properties**: Every `recv` request on a channel with at least one
  active writer eventually completes.

### Theorem 11 (Buchi x WPDS Model Checking)

The model checking problem "does the Buchi x WPDS product have an accepting
run?" is decidable in time `O(|Q_B|² × |Δ_W|³)`.

**Proof.** By Esparza et al. (2000, Theorem 4.1). The product construction
reduces Buchi acceptance to repeated reachability in the WPDS, which is
decidable via iterated poststar/prestar computations. The cubic factor comes
from the saturation procedure on the product P-automaton. ∎

### Specification Patterns

| Property | Buchi Formula | Informal |
|----------|--------------|---------|
| Response | `□(send(ch) → ◇recv(ch))` | Every send eventually matched by recv |
| Starvation | `□(ready(t) → ◇running(t))` | Every ready thread eventually runs |
| Persistence | `□(◇running(t) → □◇running(t))` | Active threads keep running |

---

## 7. Phase 6: KAT Theory

**Based on**: Kozen (1997). *Kleene algebra with tests.*

### Definition 7 (Thread KAT)

A **thread KAT** `K = (Σ_K, B_K, ·, +, *, 0, 1, ¬)` where:

- `Σ_K` is the set of actions: `{ fork, send(ch), recv(ch), new(ch), skip, fail }`.
- `B_K` is the set of tests: `{ ch_empty(ch), ch_nonempty(ch), thread_ready(t),
  thread_suspended(t), budget_available }`.
- `·` is sequential composition, `+` is nondeterministic choice, `*` is Kleene
  star (iteration), `0` is the failing program, `1` is skip.
- `¬` is test negation (complement within `B_K`).

### KAT Equations for Concurrency

The following KAT equations express thread-safety invariants:

```
(1)  send(ch) · ¬ch_empty(ch) = send(ch)
     "After send, channel is non-empty"

(2)  recv(ch) · ch_empty(ch) · skip = 0
     "Recv on empty channel with no blocking = failure"

(3)  fork · ¬budget_available = 0
     "Fork without budget = failure"

(4)  (send(ch) + recv(ch))* · ch_empty(ch) = (send(ch) · recv(ch))* · ch_empty(ch)
     "Balanced send/recv leaves channel empty"
```

### Properties Checked (beyond Phase 5)

- **Program equivalence**: Two different schedules/interleavings produce
  equivalent observable behavior (KAT equivalence is decidable via
  `PSPACE`-complete algorithm).
- **Hoare triples**: `{P} program {Q}` assertions where `P` and `Q` are KAT
  tests. For example, `{budget_available} fork {thread_ready(child)}`.
- **Refinement**: A concrete scheduler implementation refines an abstract
  specification (the concrete program's KAT denotation is contained in the
  abstract program's denotation).

### Theorem 12 (KAT Decidability)

The equational theory of KAT is decidable in `PSPACE` (Kozen & Smith, 1996).
For thread-safety properties expressed as KAT equations, verification reduces to
checking language equivalence of the corresponding automata.

**Proof.** By Kozen (1997, Theorem 5.2). KAT expressions are converted to
guarded string automata. Equivalence of KAT expressions reduces to language
equivalence of these automata, which is decidable. The PSPACE bound follows from
the exponential blowup of test complement in the worst case, but typical
thread-safety equations involve small test alphabets where the practical
complexity is manageable. ∎

---

## 8. Soundness of Pipeline Composition

### Theorem 13 (Monotone Precision)

For all phases `i < j` in the precision lattice:

```
Safe_i(G) ⟹ Safe_j(G)
```

That is, if Phase `i` proves a grammar `G` safe, then Phase `j` also proves `G`
safe.

**Proof.** By induction on the lattice order. Each phase `j` refines phase `i`
by considering strictly more information:

- Phase 1 → 2: Register automata track identity (ChannelId) in addition to names.
  Every name-correct program is also identity-correct.
- Phase 2 → 3: Petri nets model concurrent interaction structure. Every
  register-safe program has bounded channel usage in the Petri net abstraction.
- Phase 3 → 4: WPDS adds pushdown stack structure. Every bounded Petri net
  program is also reachable-safe in the WPDS (the WPDS subsumes the Petri net
  by modeling stack contexts that the Petri net abstracts away).
- Phase 4 → 5: Buchi x WPDS adds temporal properties. Every WPDS-safe program
  satisfies the liveness properties expressed as Buchi conditions (since
  reachability safety is a prerequisite for liveness).
- Phase 5 → 6: KAT adds algebraic equivalence. Every Buchi-safe program has
  equivalent behavior under KAT denotation (since KAT subsumes both safety and
  liveness via Hoare triples and Kleene iteration). ∎

### Theorem 14 (Early Termination Correctness)

If Phase `i` reports `Safe_i(G) = true`, then it is correct to skip Phases
`i+1, ..., 6` and report the grammar as safe with respect to all properties
checkable by Phase `i`.

**Proof.** Immediate from soundness of each phase. Phase `i` reports safe only
when the property holds in all concrete executions (soundness). Skipping later
phases loses only the opportunity to check additional properties that Phase `i`
cannot express, not the soundness of properties already verified. ∎

### Pipeline Decision Table

| Property | Min Phase | Phase 1 | Phase 2 | Phase 3 | Phase 4 | Phase 5 | Phase 6 |
|----------|-----------|---------|---------|---------|---------|---------|---------|
| GT01 Undefined channel | 1 | Yes | Yes | Yes | Yes | Yes | Yes |
| GT02 Send after close | 1 | Yes | Yes | Yes | Yes | Yes | Yes |
| GT03 Channel aliasing | 2 | -- | Yes | Yes | Yes | Yes | Yes |
| GT04 Register overflow | 2 | -- | Yes | Yes | Yes | Yes | Yes |
| GT05 Unbounded channel | 3 | -- | -- | Yes | Yes | Yes | Yes |
| Deadlock freedom | 3 | -- | -- | Yes | Yes | Yes | Yes |
| Dead thread detection | 4 | -- | -- | -- | Yes | Yes | Yes |
| Context-sens reachability | 4 | -- | -- | -- | Yes | Yes | Yes |
| GT06 Message starvation | 5 | -- | -- | -- | -- | Yes | Yes |
| Starvation freedom | 5 | -- | -- | -- | -- | Yes | Yes |
| Schedule equivalence | 6 | -- | -- | -- | -- | -- | Yes |
| Hoare triples | 6 | -- | -- | -- | -- | -- | Yes |

---

## 9. References

- Bojańczyk, M., Klin, B. & Lasota, S. (2014). Automata theory in nominal sets.
  *Logical Methods in Computer Science*, 10(3), pp. 1--44.
- Kaminski, M. & Francez, N. (1994). Finite-memory automata. *Theoretical
  Computer Science*, 134(2), pp. 329--363.
- Karp, R. M. & Miller, R. E. (1969). Parallel program schemata. *Journal of
  Computer and System Sciences*, 3(2), pp. 147--195.
- Reps, T., Lal, A. & Kidd, N. (2007). Program analysis using weighted pushdown
  systems. *FSTTCS*, pp. 23--51.
- Esparza, J., Hansel, D., Rossmanith, P. & Schwoon, S. (2000). Efficient
  algorithms for model checking pushdown systems. *CAV*, pp. 232--247.
- Kozen, D. (1997). Kleene algebra with tests. *ACM Transactions on Programming
  Languages and Systems*, 19(3), pp. 427--443.
- Kozen, D. & Smith, F. (1996). Kleene algebra with tests: Completeness and
  decidability. *CSL*, pp. 244--259.
- Qadeer, S. & Rehof, J. (2005). Context-bounded model checking of concurrent
  software. *TACAS*, pp. 93--107.
- Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus.*
  Cambridge University Press.
- Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the join-calculus.
  *Proceedings of POPL*, pp. 372--385.
