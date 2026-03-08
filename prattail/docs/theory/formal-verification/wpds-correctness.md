# WpdsCorrectness.v -- WPDS Poststar/Prestar Soundness

**File:** `formal/rocq/mathematical_analyses/theories/WpdsCorrectness.v`
**Lines:** 950
**Admitted:** 0
**Dependencies:** Standalone (no imports from other proof files)


## Intuition

PraTTaIL's grammar analysis uses a Weighted Pushdown System (WPDS) to
model cross-category parsing as a pushdown process. The `poststar`
algorithm computes the forward reachable configurations (what parse
stacks can arise), and `prestar` computes the backward reachable
configurations (what stacks could have led to a given target). Both
algorithms work by *saturating* a P-automaton with new transitions
until a fixpoint is reached.

The central question is: does the saturated P-automaton actually accept
*all* the stacks it should? If poststar misses a reachable configuration,
dead-rule detection gets a false negative. If prestar misses a pre-image,
context-sensitive analysis is incomplete.

This proof file establishes that both algorithms are **sound**: every
configuration that should be accepted *is* accepted by the saturated
automaton. It also proves that saturation **converges** to a fixpoint
in finitely many steps.


## What It Proves

### 1. P-Automaton Reading Relation

Foundational definitions for how a P-automaton reads a stack word
through a sequence of transitions:

| Theorem | Statement |
|---------|-----------|
| `pa_reads_monotone` | If T1 is a subset of T2, any word readable under T1 is readable under T2 |
| `pa_reads_cons_inv` | Inversion: reading gamma::w decomposes into a transition on gamma plus reading w |
| `pa_reads_app_intro` | Concatenation: reading w1 then w2 is reading w1++w2 |
| `pa_reads_app_elim` | Split: reading w1++w2 decomposes at the join point |
| `pa_reads_single` | A single transition reads a one-symbol word |

### 2. Single-Control-Location WPDS Model

PraTTaIL uses a single control location (context-free process), which
simplifies the general multi-location WPDS framework:

| Definition | Meaning |
|-----------|---------|
| `SL_Pop gamma` | Remove top of stack (rule completion) |
| `SL_Replace gamma gamma'` | Replace top (intraprocedural step) |
| `SL_Push gamma gamma1 gamma2` | Push two symbols (cross-category call) |
| `sl_step` | One-step PDS transition |
| `sl_reachable` | Reflexive-transitive closure of `sl_step` |
| `sl_trace` | Execution trace recording visited stacks |
| `sl_accepts` | P-automaton acceptance: exists a final state reachable by reading the stack word |

### 3. Poststar Soundness

**Main theorem:**

```
Theorem poststar_soundness :
  forall w,
    sl_reachable [gamma0] w ->
    sl_accepts poststar_T w.
```

If stack `w` is reachable from the initial stack `[gamma_0]`, then the
saturated P-automaton `poststar_T` accepts `w`.

### 4. Prestar Soundness

**Main theorem:**

```
Theorem prestar_soundness :
  forall w0 w,
    sl_reachable w0 w ->
    sl_accepts target_T w ->
    sl_accepts prestar_T w0.
```

If stack `w` is reachable from `w0` and `w` is accepted by the target
automaton, then the prestar automaton accepts `w0`.

### 5. MOVP Fixpoint Convergence

**Main theorem:**

```
Theorem saturation_converges :
  forall T,
    exists n, is_fixpoint (iterate n T).
```

The saturation operator reaches a fixpoint after finitely many
iterations.

### 6. Rule Structural Lemmas

Structural induction support: every rule is Pop, Replace, or Push; stack
depth changes are -1, 0, or +1 respectively; step requires a non-empty
source stack.

### 7. Poststar/Prestar Consistency

**Main theorem:**

```
Theorem poststar_prestar_consistent :
  ... ->
  sl_accepts poststar_T w /\ sl_accepts prestar_T w0.
```

If w0 reaches w and w is in the target set, then poststar accepts w
*and* prestar accepts w0. The two algorithms give consistent answers.


## Why It Matters

```
  ┌────────────────────────────────────────────────────────┐
  │  Pipeline: dead-rule detection, call-graph analysis,   │
  │  depth bounds, context-rule tables, cycle detection     │
  ├────────────────────────────────────────────────────────┤
  │  WPDS poststar / prestar                                │ <-- THIS
  ├────────────────────────────────────────────────────────┤
  │  P-automaton acceptance, saturation transitions         │ <-- THIS
  └────────────────────────────────────────────────────────┘
```

The WPDS module (`wpds.rs`, ~3150 lines) is the engine behind:

- **Dead-rule detection:** unreachable rules have no poststar witness
- **Call-graph construction:** SCC analysis of cross-category calls
- **Depth bound analysis:** stack depth tracks nesting depth
- **Context-sensitive BP:** binding power propagation along WPDS paths
- **Cycle classification:** recursive vs. mutually recursive rules

If poststar is unsound, rules that are actually reachable would be
flagged as dead. If prestar is unsound, context information would be
incomplete. If saturation does not converge, the pipeline hangs.


## Proof Strategy

### Poststar: Induction on Reachability

The proof proceeds in two layers:

**Layer 1 -- One-step preservation** (`poststar_step_forward`):

For each rule form, show that if `w1` is accepted and `w1 -> w2`, then
`w2` is accepted:

```
┌──────────────────────────────────────────────────────────────────┐
│ Case: SL_Pop gamma                                               │
│                                                                  │
│  w1 = gamma :: w,  w2 = w                                        │
│                                                                  │
│  Hreads: pa_reads T embed_p (gamma :: w) q_f                     │
│  Decompose: (embed_p, gamma, q_mid) in T                         │
│             pa_reads T q_mid w q_f                                │
│  By pop_absorption: pa_reads T embed_p w q_f                     │
│                                                                  │
├──────────────────────────────────────────────────────────────────┤
│ Case: SL_Replace gamma gamma'                                    │
│                                                                  │
│  w1 = gamma :: w,  w2 = gamma' :: w                              │
│                                                                  │
│  Decompose: (embed_p, gamma, q_mid) in T                         │
│  By sat_replace: (embed_p, gamma', q_mid) in T                   │
│  Construct: pa_reads T embed_p (gamma' :: w) q_f                 │
│                                                                  │
├──────────────────────────────────────────────────────────────────┤
│ Case: SL_Push gamma gamma1 gamma2                                │
│                                                                  │
│  w1 = gamma :: w,  w2 = gamma1 :: gamma2 :: w                    │
│                                                                  │
│  Decompose: (embed_p, gamma, q_mid) in T                         │
│  By sat_push: exists q_r,                                        │
│    (embed_p, gamma1, q_r) in T  and  (q_r, gamma2, q_mid) in T  │
│  Construct: read gamma1 to q_r, read gamma2 to q_mid, read w    │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

**Layer 2 -- Reachability propagation** (`poststar_reachable_preserves`):

By induction on the reachability derivation, apply Layer 1 at each step.
The base case is the initial configuration `[gamma_0]`, which is accepted
by `init_trans` and `init_final`.

### Saturation Rule Diagram

The following diagram illustrates how poststar adds transitions for each
rule type. The P-automaton starts with the transition `(embed_p, gamma_0,
q_final)` and grows by applying saturation conditions:

```
         Replace: gamma -> gamma'
         ─────────────────────────

  Before:    embed_p ──gamma──> q

  After:     embed_p ──gamma──> q
             embed_p ──gamma'─> q      (new)


         Push: gamma -> gamma1 gamma2
         ─────────────────────────────

  Before:    embed_p ──gamma──> q

  After:     embed_p ──gamma──> q
             embed_p ──gamma1─> q_r    (new, fresh q_r)
             q_r ─────gamma2─> q       (new)


         Pop: gamma -> epsilon
         ─────────────────────

  Before:    embed_p ──gamma──> q
             q ──────sigma──> q'  (for any sigma, q')

  After:     embed_p ──sigma──> q'     (absorption: paths from q
                                        are reproduced from embed_p)
```

### Prestar: Backward Induction

Prestar works in the opposite direction. The key lemma
`prestar_step_back` shows: if `w1 -> w2` and `w2` is accepted, then
`w1` is accepted.

- **Pop:** By `sat_pre_pop`, `(embed_p, gamma, embed_p)` is in the
  prestar transition set. Prefix the read of `w` with this self-loop.
- **Replace:** By `sat_pre_replace`, the LHS transition `(embed_p,
  gamma, q)` is added whenever the RHS transition `(embed_p, gamma', q)`
  exists.
- **Push:** By `sat_pre_push`, when consecutive transitions for gamma1
  and gamma2 exist, the LHS transition for gamma is added.

The main theorem follows by induction on reachability, applying the
step-back lemma, with the target acceptance lifted via monotonicity.

### MOVP Convergence: Well-Founded Induction on the Gap

The saturation operator is monotone (only adds transitions) and the
set of possible transitions is finite (bounded by `max_transitions`).
At each non-fixpoint step, the transition set grows strictly (by
`not_fixpoint_grows`). The proof uses well-founded induction on the
quantity `max_transitions - length(iterate n T)`:

```
  fuel = max_transitions - |T_n|

  If fuel = 0 and not a fixpoint:
    T_{n+1} would exceed max_transitions -- contradiction.

  If fuel = S fuel':
    Either T_n is a fixpoint (done), or T_{n+1} has fuel' < fuel
    remaining -- recurse.
```

This is the only proof in the file that uses classical logic
(`From Stdlib Require Import Classical`), specifically the `classic`
axiom for the decidability of `is_fixpoint`.


## Rust Code Traceability

| Rocq Definition | Rust Counterpart | File |
|----------------|-----------------|------|
| `symbol` | `StackSymbol { category, rule_label, position }` | `wpds.rs:62-69` |
| `SL_Pop/Replace/Push` | `WpdsRule::Pop/Replace/Push` | `wpds.rs:104-133` |
| `sl_step` | One-step PDS execution logic | `wpds.rs:101-103` |
| `sl_reachable` | Reflexive-transitive closure | `wpds.rs:689-706` |
| `pa_reads` | P-automaton path traversal | `wpds.rs:248-254` |
| `sl_accepts` | `PAutomaton` acceptance check | `wpds.rs:314-324` |
| `poststar_T` | Saturated transition `HashMap` | `wpds.rs:724-729` |
| `sat_step` | Worklist iteration body | `wpds.rs:735-836` |
| `embed_p` | `p_state = 0` | `wpds.rs:709` |
| `sat_replace` | Replace-rule saturation case | `wpds.rs:750-777` |
| `sat_push` | Push-rule saturation case | `wpds.rs:779-834` |
| `sat_pre_pop` | Pop-rule prestar Phase 1 | `wpds.rs:874-898` |
| `sat_pre_replace` | Replace-rule prestar case | `wpds.rs:916-951` |
| `sat_pre_push` | Push-rule prestar case | `wpds.rs:953-998` |


## Key Modeling Decision: Single Control Location

PraTTaIL's `build_wpds` (wpds.rs:388-644) always uses a single control
location `p = p'` (context-free process). The proof exploits this by:

1. Omitting the control state from rule representations
2. Using a single `embed_p` state in the P-automaton
3. Simplifying Pop handling (the sub-stack stays under the same control)

This matches the Rust implementation exactly and avoids the complexity of
the general multi-location framework from Reps, Lal & Kidd (2007), which
would introduce inter-location transitions that PraTTaIL never generates.
