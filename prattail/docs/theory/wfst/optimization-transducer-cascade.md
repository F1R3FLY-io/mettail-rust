# Optimization Transducer Cascade (E1)

> **Date:** 2026-03-01

The optimization transducer cascade represents each post-construction
optimization of a prediction WFST as a composable transducer -- a
function from WFSTs to WFSTs -- and sequences them into a fixed-point
pipeline that iterates until the WFST stabilizes. The cascade is
labelled **E1** in the codebase.

---

## Table of Contents

1.  [The Multi-Pass Optimization Problem](#1-the-multi-pass-optimization-problem)
2.  [Formal Definitions](#2-formal-definitions)
    - 2.1 [Optimization Pass as a WFST Endomorphism](#21-optimization-pass-as-a-wfst-endomorphism)
    - 2.2 [State-Count Measure Function](#22-state-count-measure-function)
    - 2.3 [Change Count](#23-change-count)
3.  [Composition Algebra](#3-composition-algebra)
    - 3.1 [Sequential Composition](#31-sequential-composition)
    - 3.2 [Identity Pass and Identity Composition](#32-identity-pass-and-identity-composition)
    - 3.3 [Associativity](#33-associativity)
    - 3.4 [Non-Commutativity](#34-non-commutativity)
4.  [Fixed-Point Convergence Proof](#4-fixed-point-convergence-proof)
    - 4.1 [Monotonicity Lemma](#41-monotonicity-lemma)
    - 4.2 [Lower Bound Lemma](#42-lower-bound-lemma)
    - 4.3 [Convergence Theorem](#43-convergence-theorem)
    - 4.4 [Safety Bound](#44-safety-bound)
5.  [Language-Preservation Theorem](#5-language-preservation-theorem)
    - 5.1 [Dispatch Semantics](#51-dispatch-semantics)
    - 5.2 [Per-Pass Preservation](#52-per-pass-preservation)
    - 5.3 [Compositional Preservation](#53-compositional-preservation)
6.  [Built-in Passes as Transducers](#6-built-in-passes-as-transducers)
    - 6.1 [T_normalize: Weight Normalization](#61-t_normalize-weight-normalization)
    - 6.2 [T_dead_elim: Dead-State Elimination](#62-t_dead_elim-dead-state-elimination)
    - 6.3 [T_minimize: State Minimization](#63-t_minimize-state-minimization)
    - 6.4 [T_beam_prune: Beam Pruning](#64-t_beam_prune-beam-pruning)
7.  [Priority Ordering and Pass Sequencing](#7-priority-ordering-and-pass-sequencing)
8.  [Worked Example: 3-Pass Cascade on a 5-State WFST](#8-worked-example-3-pass-cascade-on-a-5-state-wfst)
9.  [Complexity Analysis](#9-complexity-analysis)
    - 9.1 [Per-Iteration Cost](#91-per-iteration-cost)
    - 9.2 [Total Cost to Convergence](#92-total-cost-to-convergence)
    - 9.3 [Per-Pass Breakdown](#93-per-pass-breakdown)
10. [Source References](#10-source-references)
11. [Cross-References](#11-cross-references)

---

## 1. The Multi-Pass Optimization Problem

### 1.1 Phenomenon

After constructing a prediction WFST from FIRST sets and dispatch
action tables, the raw transducer may contain redundancies:

- **Unreachable states:** states that cannot be reached from the start
  state, or that have no path to a final state. These arise when union
  operations merge independently-constructed sub-WFSTs.
- **Equivalent states:** distinct states with identical observable
  behaviour (same is_final flag, same final weight, same outgoing
  transition signatures). These can be merged without altering the
  transducer's input-output mapping.
- **Suboptimal weight scales:** transition weights may not be
  zero-aligned (the best transition from a state may have a nonzero
  weight), complicating downstream beam pruning thresholds.
- **Low-probability transitions:** transitions with weights far from
  the best alternative per state are unlikely to be selected at
  runtime and waste dispatch resources.

Each of these redundancies is addressed by a specialized optimization
pass. However, passes interact: dead-state elimination may expose new
equivalences for minimization; minimization may make previously-marginal
transitions dominant after weight normalization; beam pruning may
render states unreachable. Running each pass once in isolation leaves
cross-pass improvement opportunities on the table.

### 1.2 The Cascade Solution

The transducer cascade composes all passes into a pipeline and iterates
until a fixed point is reached -- i.e. no pass makes any changes on
a full sweep. This guarantees that all cross-pass interactions have
been fully exploited.

```
W₀  ──► T_normalize ──► T_dead_elim ──► T_minimize ──► T_beam_prune ──► W₁
                                                                        │
                               ┌────────────────────────────────────────┘
                               │
                               ▼  any changes?
                              ╱╲
                             ╱  ╲
                          yes    no ──► converged: return W₁
                             ╲  ╱
                              ╲╱
                               │
                               ▼
W₁  ──► T_normalize ──► T_dead_elim ──► T_minimize ──► T_beam_prune ──► W₂
                               ...
```

---

## 2. Formal Definitions

### 2.1 Optimization Pass as a WFST Endomorphism

Let **W** denote the set of all well-formed prediction WFSTs
(finite-state, with a designated start state, non-negative tropical
weights, and an action table). An **optimization pass** is a function:

```
T : W → W
```

That is, T takes a WFST and produces another WFST. We call T an
**endomorphism** on W because the domain and codomain are the same set.

In the implementation, this corresponds to the `OptimizationPass` trait
(`transducer.rs`, line 78):

```
trait OptimizationPass {
    fn name(&self) -> &str;
    fn priority(&self) -> u32;
    fn is_applicable(&self, wfst: &PredictionWfst) -> bool;
    fn apply(&self, wfst: &mut PredictionWfst) -> PassResult;
}
```

The `apply` method mutates the WFST in place (for efficiency), but
semantically it maps W to T(W).

When `is_applicable` returns false for a given WFST, the pass acts as
the identity function on that input:

```
T(W) = W     when ¬is_applicable(W)
```

### 2.2 State-Count Measure Function

Define the **measure function** mu on WFSTs:

```
mu(W) = |W.states|
```

where `|W.states|` is the number of states in W. This function has
the following properties:

1. **Non-negativity:** mu(W) >= 0 for all W in W.
2. **Integrality:** mu(W) is a natural number.
3. **Computability:** mu(W) is trivially computed in O(1) via
   `PredictionWfst::state_count()` (`wfst.rs`, line 532).

We also define the **transition-count measure**:

```
tau(W) = sum over s in W.states of |s.transitions|
```

The combined measure nu(W) = (mu(W), tau(W)) provides a finer-grained
monotonicity witness (see Section 4).

### 2.3 Change Count

Each pass returns a `PassResult` (`transducer.rs`, line 46) containing
a `changes: usize` field. The cascade uses this as the convergence
indicator:

```
converged(iteration) <==> sum_{T in passes} T.changes == 0
```

An iteration with zero total changes across all passes means no pass
modified the WFST, hence the WFST is at a fixed point.

---

## 3. Composition Algebra

### 3.1 Sequential Composition

Given two optimization passes T1, T2 : W -> W, their **sequential
composition** is denoted:

```
(T1 . T2)(W) = T1(T2(W))
```

That is, T2 is applied first, then T1 is applied to the result. This
follows the standard mathematical convention where `f . g` means
"apply g first, then f."

In the cascade, passes are applied in priority order (lower priority
number = runs first). For the default pipeline:

```
cascade(W) = T_minimize(T_dead_elim(T_normalize(W)))
           = (T_minimize . T_dead_elim . T_normalize)(W)
```

### 3.2 Identity Pass and Identity Composition

Define the **identity pass** Id : W -> W by:

```
Id(W) = W     for all W in W
```

Id makes zero changes to the WFST. Composition with the identity
satisfies:

```
T . Id = T
Id . T = T
```

**Proof.** For any W in W:

```
(T . Id)(W) = T(Id(W)) = T(W)
(Id . T)(W) = Id(T(W)) = T(W)
```

Both directions hold by the definition of Id.  []

In practice, when `is_applicable` returns false, a pass degenerates to
Id on that input. The cascade handles this transparently: the pass
contributes zero changes and the iteration continues with the next pass
(`transducer.rs`, lines 363--374).

### 3.3 Associativity

Composition of WFST endomorphisms is associative:

```
(T1 . T2) . T3 = T1 . (T2 . T3)
```

**Proof.** For any W in W:

```
((T1 . T2) . T3)(W)
  = (T1 . T2)(T3(W))
  = T1(T2(T3(W)))

(T1 . (T2 . T3))(W)
  = T1((T2 . T3)(W))
  = T1(T2(T3(W)))
```

Both expressions reduce to T1(T2(T3(W))).  []

This means the cascade need not parenthesize the pass sequence
explicitly; left-to-right application in a loop is sufficient.

### 3.4 Non-Commutativity

Optimization pass composition is generally **not** commutative:

```
T1 . T2  =/=  T2 . T1     in general
```

For example, applying beam pruning before dead-state elimination may
leave unreachable states that dead-state elimination would have removed
first (enabling beam pruning to operate on a smaller WFST). The fixed-
point cascade mitigates ordering sensitivity by iterating, but the
*number* of iterations to convergence depends on pass ordering. Priority
ordering (Section 7) is chosen to minimize iteration count.

---

## 4. Fixed-Point Convergence Proof

### 4.1 Monotonicity Lemma

**Lemma (Monotone Decrease).** For every built-in optimization pass T
and every WFST W in W:

```
mu(T(W)) <= mu(W)
```

and

```
tau(T(W)) <= tau(W)
```

That is, each pass can only remove states or transitions, never add
them.

**Proof.** By case analysis on the four built-in passes:

**Case T_normalize (WeightNormalization).** This pass subtracts a
constant from transition weights within each state. It does not add,
remove, or redirect any transitions or states. Therefore
mu(T_normalize(W)) = mu(W) and tau(T_normalize(W)) = tau(W). Both
inequalities hold trivially (with equality).

**Case T_dead_elim (DeadStateElimination).** This pass performs forward
reachability from the start state and removes any states not in the
reachable set. Removing states strictly decreases mu (when any
unreachable states exist) and removes their outgoing transitions,
decreasing tau. When no unreachable states exist, both measures are
unchanged. Therefore mu(T_dead_elim(W)) <= mu(W) and
tau(T_dead_elim(W)) <= tau(W).

**Case T_minimize (StateMinimization).** This pass computes
signature-based equivalence classes and merges states within each class
to a single representative. The number of states after minimization
equals the number of distinct equivalence classes, which is at most
the number of states before minimization. Transitions pointing to
merged states are redirected to the representative; the set of
transitions per remaining state does not grow (identical transitions
from the same source are deduplicated by the signature). Therefore
mu(T_minimize(W)) <= mu(W) and tau(T_minimize(W)) <= tau(W).

**Case T_beam_prune (BeamPruning).** This pass removes transitions
whose weight exceeds the per-state best weight plus the beam width.
It does not add transitions. States left with no outgoing transitions
are not removed by this pass itself, but may become dead states
removable by T_dead_elim on the next iteration. Therefore
tau(T_beam_prune(W)) <= tau(W). Since no states are removed:
mu(T_beam_prune(W)) = mu(W).  []

### 4.2 Lower Bound Lemma

**Lemma (Lower Bound).** For every WFST W in W:

```
mu(W) >= 1
```

**Proof.** Every well-formed prediction WFST has at least one state:
the start state. The `PredictionWfstBuilder::build()` always creates
a start state (`wfst.rs`, line 530 et seq.), and no optimization pass
removes the start state (the start state is always reachable from
itself, is always its own representative in minimization, and beam
pruning does not remove states). Therefore mu(W) >= 1 for all W
reachable from any initial WFST through any sequence of optimization
passes.  []

Similarly:

```
tau(W) >= 0
```

A WFST with a single isolated start state has zero transitions.

### 4.3 Convergence Theorem

**Theorem (Fixed-Point Convergence).** Let W0 be an initial WFST and
let C = T_k . T_{k-1} . ... . T_1 be a cascade of k optimization
passes, each satisfying the monotonicity lemma. Define:

```
W_{i+1} = C(W_i)     for i = 0, 1, 2, ...
```

Then there exists n <= mu(W0) - 1 such that W_{n+1} = W_n (the cascade
has converged to a fixed point).

**Proof.** Consider the sequence of measures:

```
mu(W0), mu(W1), mu(W2), ...
```

By the monotonicity lemma applied to each pass in the cascade:

```
mu(W_{i+1}) = mu(C(W_i)) <= mu(W_i)
```

so the sequence is non-increasing. By the lower bound lemma:

```
mu(W_i) >= 1     for all i
```

A non-increasing sequence of natural numbers bounded below by 1 can
decrease at most mu(W0) - 1 times before it must stabilize. Once
mu stabilizes (mu(W_{i+1}) = mu(W_i)), we consider tau:

```
tau(W_{i+1}) <= tau(W_i)
```

tau is also a non-increasing sequence of natural numbers bounded below
by 0. Once both mu and tau stabilize, no pass makes any structural
changes, so the change count is zero, and the cascade loop terminates.

The cascade converges in at most:

```
n <= mu(W0) + tau(W0) - 1
```

iterations. In practice, convergence is much faster: typically 2
iterations (one productive, one confirming the fixed point).  []

### 4.4 Safety Bound

The implementation includes a safety bound (`max_iterations`, default
100) to guard against pathological cases or future passes that might
violate monotonicity (`transducer.rs`, line 304):

```rust
max_iterations: usize,  // default: 100
```

The convergence theorem guarantees this bound is never reached for the
built-in passes on any prediction WFST constructed by the PraTTaIL
pipeline, since mu(W0) is always far less than 100 for practical
grammars.

---

## 5. Language-Preservation Theorem

### 5.1 Dispatch Semantics

The **dispatch semantics** of a prediction WFST W is the function:

```
dispatch_W : Sigma -> List<(DispatchAction, TropicalWeight)>
```

mapping each token to an ordered list of (action, weight) pairs. Two
WFSTs W and W' have **equivalent dispatch semantics** if for every
token t in Sigma:

```
best_action(dispatch_W(t)) = best_action(dispatch_W'(t))
```

where `best_action` selects the action with the minimum tropical weight
(ties broken by declaration order).

### 5.2 Per-Pass Preservation

**Theorem (Per-Pass Semantic Preservation).** Each built-in optimization
pass preserves dispatch semantics.

**Proof.** By case analysis:

**Case T_normalize.** Weight normalization subtracts the per-state
minimum weight from all transitions leaving that state. For the start
state (the single dispatch point), all transitions have the same
constant subtracted. This preserves relative ordering:

```
w_a < w_b  <==>  (w_a - min) < (w_b - min)
```

Therefore the best action for each token is unchanged. Since only the
start state matters for dispatch, normalization at other states is
vacuous for dispatch semantics but consistent for internal WFST
structure.  []

**Case T_dead_elim.** Dead-state elimination removes only states that
are unreachable from the start state. No transition from the start
state targets an unreachable state (by definition of reachability).
Therefore the set of transitions from the start state -- and hence the
dispatch mapping -- is unchanged.  []

**Case T_minimize.** State minimization merges states with identical
signatures. Two states with the same (is_final, final_weight,
sorted_transitions) have identical observable behaviour. Merging them
redirects transitions to the representative, but since both source and
target had identical signatures, the dispatch mapping at the start
state is preserved: each token still maps to the same action with the
same weight.  []

**Case T_beam_prune.** Beam pruning removes transitions whose weight
exceeds `best_weight + beam_width` from their source state. By
definition, the best-weight transition is never pruned. Therefore for
each token, the best action is preserved. Suboptimal actions outside
the beam are removed, but these are strictly worse alternatives that
would not be selected by the dispatch protocol.

Note: beam pruning *does* alter the set of available alternatives (it
may remove fallback paths). This is an intentional trade-off: the
removed alternatives have high weight and are unlikely to succeed. The
*best* action is always preserved.  []

### 5.3 Compositional Preservation

**Corollary.** The full cascade preserves dispatch semantics.

**Proof.** Each individual pass preserves dispatch semantics (Section
5.2). Composition of semantics-preserving functions is semantics-
preserving:

```
dispatch_{T1(T2(W))} = dispatch_{T2(W)} = dispatch_W
```

By induction on the number of passes and the number of iterations,
the full cascade preserves dispatch semantics.  []

---

## 6. Built-in Passes as Transducers

Each built-in pass can be understood as a WFST-to-WFST transducer with
specific structural properties.

### 6.1 T_normalize: Weight Normalization

| Property       | Value                                                                           |
|:---------------|:--------------------------------------------------------------------------------|
| Priority       | 5 (runs first)                                                                  |
| Applicability  | state_count > 0                                                                 |
| Effect         | For each state s, subtract min_{t in s.transitions} w(t) from all w(t)          |
| Monotonicity   | mu unchanged, tau unchanged (weight-only transform)                             |
| Idempotent     | Yes -- after normalization, min weight = 0.0, so re-normalization has no effect |
| Implementation | `WeightNormalization` (`transducer.rs`, line 234)                               |

**Formal specification.** For each state s in W.states:

```
min_s = min { w(t) : t in s.transitions }

T_normalize(s).transitions = { (t.from, t.input, t.action_idx, t.to, w(t) - min_s) :
                                t in s.transitions }
```

The subtraction preserves relative ordering within the tropical semiring
because the tropical weight carrier set (non-negative reals with
infinity) is closed under subtraction when the minimum is subtracted:

```
w(t) - min_s >= 0     for all t, since w(t) >= min_s
```

The implementation also updates the action table weights to match
(`wfst.rs`, lines 624--649).

### 6.2 T_dead_elim: Dead-State Elimination

| Property       | Value                                                                               |
|:---------------|:------------------------------------------------------------------------------------|
| Priority       | 10 (runs after normalization)                                                       |
| Applicability  | state_count > 2                                                                     |
| Effect         | Remove states unreachable from the start state                                      |
| Monotonicity   | mu strictly decreases (when dead states exist), tau decreases                       |
| Idempotent     | Yes -- after elimination, all states are reachable, so re-elimination has no effect |
| Implementation | `DeadStateElimination` (`transducer.rs`, line 113)                                  |

**Formal specification.** Compute the set of reachable states via
forward BFS/DFS from the start state:

```
Reachable = { s in Q : there exists a path from start to s in delta }
```

Then:

```
T_dead_elim(W).states = { s in W.states : s in Reachable }
T_dead_elim(W).transitions = { t in W.transitions : t.from in Reachable and t.to in Reachable }
```

State IDs are compacted after removal (`wfst.rs`, lines 555--594).

The BooleanWeight semiring provides the algebraic framework for this
analysis: assign BooleanWeight::one() (true) to the start state and
propagate through transitions. A state is reachable iff its accumulated
BooleanWeight is one().

### 6.3 T_minimize: State Minimization

| Property       | Value                                                                    |
|:---------------|:-------------------------------------------------------------------------|
| Priority       | 20 (runs after dead-state elimination)                                   |
| Applicability  | state_count > 2                                                          |
| Effect         | Merge states with identical signatures                                   |
| Monotonicity   | mu decreases (when equivalent states exist), tau may decrease            |
| Idempotent     | Yes -- after minimization, all remaining states have distinct signatures |
| Implementation | `StateMinimization` (`transducer.rs`, line 156)                          |

**Formal specification.** Define the **state signature**:

```
sig(s) = (s.is_final, bits(s.final_weight), sorted({ (t.input, t.action_idx, t.to, bits(t.weight)) :
                                                       t in s.transitions }))
```

where `bits(w)` is the IEEE 754 bit pattern of the f64 weight (for
exact equality without floating-point comparison issues).

Two states s1, s2 are **equivalent** iff sig(s1) = sig(s2).

The minimization algorithm (`wfst.rs`, lines 437--528):
1. Compute sig(s) for every state s.
2. For each unique signature, select the first state encountered as
   the representative.
3. Redirect all transitions pointing to non-representative states to
   their representative.
4. Remove non-representative states.
5. Compact state IDs.

This is a single-pass signature-based algorithm, not the classical
Hopcroft algorithm, because the prediction WFSTs are typically small
(tens to low hundreds of states). The complexity is
O(|S| * |T| * log(|T|)) due to transition sorting within signatures.

### 6.4 T_beam_prune: Beam Pruning

| Property       | Value                                                               |
|:---------------|:--------------------------------------------------------------------|
| Priority       | 30 (runs after minimization)                                        |
| Applicability  | beam_width is finite and state_count > 0                            |
| Effect         | Remove transitions with weight > best + beam_width                  |
| Monotonicity   | mu unchanged (no state removal), tau decreases                      |
| Idempotent     | Yes -- after pruning, all remaining transitions are within the beam |
| Implementation | `BeamPruning` (`transducer.rs`, line 187)                           |

**Formal specification.** For each state s:

```
best_s = min { w(t) : t in s.transitions }

T_beam_prune(s).transitions = { t in s.transitions : w(t) <= best_s + beam_width }
```

The beam width is a compile-time parameter set in the grammar
specification (`transducer.rs`, line 189). In the cascade, beam pruning
runs after weight normalization has aligned the best weight to 0.0, so
the effective threshold is simply `beam_width`:

```
After T_normalize: best_s = 0.0
Beam threshold: 0.0 + beam_width = beam_width
```

Pruned transitions may leave target states unreachable. These become
dead states, discoverable by T_dead_elim on the next iteration. This
is the primary source of cross-pass interaction in the cascade.

---

## 7. Priority Ordering and Pass Sequencing

Each pass declares a priority (lower = runs first). The cascade sorts
passes by priority on insertion (`transducer.rs`, lines 340--343):

```rust
pub fn add_pass(&mut self, pass: Box<dyn OptimizationPass>) {
    self.passes.push(pass);
    self.passes.sort_by_key(|p| p.priority());
}
```

The default pipeline ordering and its rationale:

```
Priority  Pass                  Rationale
────────  ────────────────────  ──────────────────────────────────────────────
   5      T_normalize           Zero-align weights before any structural
                                analysis, so beam thresholds are meaningful
                                and signature comparison is canonical.
  10      T_dead_elim           Remove unreachable states early so that
                                subsequent passes operate on a smaller WFST.
  20      T_minimize            Merge equivalent states after dead-state
                                removal has cleaned up the state space.
  30      T_beam_prune          Prune low-priority transitions last, after
                                normalization and minimization have settled
                                the weight landscape. (Only included when
                                beam_width is configured.)
```

This ordering is designed to minimize iteration count:

1. **Normalization first** ensures canonical weights for all subsequent
   passes. Since normalization is idempotent and does not change
   structure, it never triggers additional iterations on its own.

2. **Dead-state elimination before minimization** reduces the state
   space so that minimization's O(|S| * |T| * log|T|) cost is applied
   to a smaller input.

3. **Minimization before beam pruning** ensures that the beam operates
   on a minimal WFST, so the fewest possible transitions need
   examination.

4. **Beam pruning last** because it is the only pass that can create
   new dead states (by severing the sole path to a target state). If
   it creates dead states, the cascade re-runs from T_normalize,
   T_dead_elim cleans them up, and T_minimize may find new equivalences.

In practice, most grammars converge in 2 iterations: iteration 1
performs the actual optimizations, iteration 2 confirms no further
changes (the zero-change confirmation sweep).

---

## 8. Worked Example: 3-Pass Cascade on a 5-State WFST

### 8.1 Initial WFST W0

Consider a prediction WFST for category `Expr` with the following
structure (constructed after union of two sub-WFSTs):

```
               w=3.0            w=5.0             w=3.0
     ┌──────── Ident ──────► q1 [final]    ┌───── Ident ──────► q3 [final]
     │                                     │
q0 (start)                             q2 (start of unioned WFST)
     │                                     │
     └──────── Int ────────► q1 [final]    └───── Bool ───────► q4 [final]
               w=1.0                              w=7.0
```

After the `union()` operation, the combined WFST has:

```
             w=3.0
  ┌──────── Ident ──────► q1 [final, w_f=0.0]
  │
  │          w=1.0
  ├──────── Int ────────► q1 [final, w_f=0.0]
  │
q0 (start)
  │          w=3.0
  ├──────── Ident ──────► q3 [final, w_f=0.0]
  │
  │          w=7.0
  └──────── Bool ───────► q4 [final, w_f=0.0]
            (q2 absorbed into q0 by union)
```

mu(W0) = 4 (states: q0, q1, q3, q4), tau(W0) = 4 (transitions).

### 8.2 Iteration 1

**Pass 1: T_normalize (priority 5).**

The start state q0 has transitions with weights {3.0, 1.0, 3.0, 7.0}.
The minimum is 1.0. Subtract 1.0 from all:

```
             w=2.0
  ┌──────── Ident ──────► q1 [final]
  │
  │          w=0.0
  ├──────── Int ────────► q1 [final]
  │
q0 (start)
  │          w=2.0
  ├──────── Ident ──────► q3 [final]
  │
  │          w=6.0
  └──────── Bool ───────► q4 [final]
```

Result: 1 state normalized. mu = 4, tau = 4.

**Pass 2: T_dead_elim (priority 10).**

Forward reachability from q0: {q0, q1, q3, q4} -- all states are
reachable. Result: 0 changes. mu = 4, tau = 4.

**Pass 3: T_minimize (priority 20).**

Compute signatures:
- sig(q0) = (false, 0.0-bits, [(Ident, act_0, q1, 2.0), (Int, act_1, q1, 0.0), (Ident, act_2, q3, 2.0), (Bool, act_3, q4, 6.0)])
- sig(q1) = (true, 0.0-bits, [])
- sig(q3) = (true, 0.0-bits, [])
- sig(q4) = (true, 0.0-bits, [])

States q1, q3, q4 all have signature (true, 0.0-bits, []) -- they are
equivalent! Select q1 as the representative. Redirect:

```
             w=2.0
  ┌──────── Ident ──────► q1 [final]
  │
  │          w=0.0
  ├──────── Int ────────► q1 [final]
  │
q0 (start)
  │          w=2.0
  ├──────── Ident ──────► q1 [final]    (was q3, now q1)
  │
  │          w=6.0
  └──────── Bool ───────► q1 [final]    (was q4, now q1)
```

Remove orphaned states q3, q4:

```
             w=2.0
  ┌──────── Ident ──────► q1 [final]
  │
  │          w=0.0
  ├──────── Int ────────► q1 [final]
  │
q0 (start)
  │          w=2.0
  ├──────── Ident ──────► q1 [final]
  │
  │          w=6.0
  └──────── Bool ───────► q1 [final]
```

Result: 2 states merged. mu = 2, tau = 4.

Iteration 1 total changes: 1 + 0 + 2 = 3.

### 8.3 Iteration 2

**Pass 1: T_normalize.** Best weight is already 0.0. No change.

**Pass 2: T_dead_elim.** state_count = 2, not applicable (threshold
is > 2). No change.

**Pass 3: T_minimize.** state_count = 2, not applicable. No change.

Iteration 2 total changes: 0. **Converged.**

### 8.4 Summary

```
┌─────────────┬──────┬──────┬─────────────────────────────┐
│ Iteration   │  mu  │  tau │ Changes                     │
├─────────────┼──────┼──────┼─────────────────────────────┤
│ W0 (input)  │   4  │   4  │ —                           │
│ After iter 1│   2  │   4  │ 3 (normalize:1, minimize:2) │
│ After iter 2│   2  │   4  │ 0 (fixed point)             │
└─────────────┴──────┴──────┴─────────────────────────────┘
```

The cascade reduced the WFST from 4 states to 2 states in 2 iterations.

---

## 9. Complexity Analysis

### 9.1 Per-Iteration Cost

Let k = number of passes, |S| = number of states, |T| = number of
transitions. The per-iteration cost is:

```
C_iteration = sum_{j=1}^{k} C(T_j)
```

where C(T_j) is the cost of pass j. Since each pass examines all
states and/or transitions:

```
C_iteration = O(k * (|S| + |T|))
```

with an additional O(|T| * log|T|) factor for minimization's
signature sorting.

### 9.2 Total Cost to Convergence

By the convergence theorem (Section 4.3), the cascade runs at most
mu(W0) iterations. Therefore the total cost is:

```
C_total = O(mu(W0) * k * (|S_0| + |T_0| + |T_0| * log|T_0|))
```

Since mu(W0) = |S_0|, this simplifies to:

```
C_total = O(|S_0| * k * |T_0| * log|T_0|)
```

In practice, mu(W0) is small (typically < 50 for PraTTaIL grammars),
k = 3 or 4, and convergence occurs in 2 iterations, so the effective
cost is:

```
C_practical = O(2 * k * (|S| + |T| * log|T|))
            = O(k * |T| * log|T|)
```

### 9.3 Per-Pass Breakdown

| Pass         | Time Complexity             | Space Complexity | Bottleneck               |
|:-------------|:----------------------------|:-----------------|:-------------------------|
| T_normalize  | O(\|S\| + \|T\|)            | O(1) extra       | Linear scan              |
| T_dead_elim  | O(\|S\| + \|T\|)            | O(\|S\|) visited | BFS/DFS traversal        |
| T_minimize   | O(\|S\| * \|T\| * log\|T\|) | O(\|S\| + \|T\|) | Signature hashing + sort |
| T_beam_prune | O(\|S\| + \|T\|)            | O(1) extra       | Linear scan + retain     |

The dominant cost is T_minimize's signature computation and comparison.
For the typical PraTTaIL prediction WFST (start state + N final states,
O(N) transitions), this reduces to O(N * log N).

---

## 10. Source References

| Symbol / Function                             | Location                     | Line(s) |
|:----------------------------------------------|:-----------------------------|--------:|
| `OptimizationPass` trait                      | `prattail/src/transducer.rs` |      78 |
| `OptimizationPass::name()`                    | `prattail/src/transducer.rs` |      80 |
| `OptimizationPass::priority()`                | `prattail/src/transducer.rs` |      84 |
| `OptimizationPass::is_applicable()`           | `prattail/src/transducer.rs` |      92 |
| `OptimizationPass::apply()`                   | `prattail/src/transducer.rs` |     100 |
| `PassResult`                                  | `prattail/src/transducer.rs` |      46 |
| `PassResult::unchanged()`                     | `prattail/src/transducer.rs` |      55 |
| `PassResult::changed()`                       | `prattail/src/transducer.rs` |      63 |
| `WeightNormalization`                         | `prattail/src/transducer.rs` |     234 |
| `DeadStateElimination`                        | `prattail/src/transducer.rs` |     113 |
| `StateMinimization`                           | `prattail/src/transducer.rs` |     156 |
| `BeamPruning`                                 | `prattail/src/transducer.rs` |     187 |
| `TransducerCascade`                           | `prattail/src/transducer.rs` |     300 |
| `TransducerCascade::new()`                    | `prattail/src/transducer.rs` |     309 |
| `TransducerCascade::default_pipeline()`       | `prattail/src/transducer.rs` |     322 |
| `TransducerCascade::with_beam()`              | `prattail/src/transducer.rs` |     331 |
| `TransducerCascade::add_pass()`               | `prattail/src/transducer.rs` |     340 |
| `TransducerCascade::run()`                    | `prattail/src/transducer.rs` |     353 |
| `TransducerCascade::run_all()`                | `prattail/src/transducer.rs` |     394 |
| `PredictionWfst::state_count()`               | `prattail/src/wfst.rs`       |     532 |
| `PredictionWfst::reachable_state_count()`     | `prattail/src/wfst.rs`       |     537 |
| `PredictionWfst::remove_unreachable_states()` | `prattail/src/wfst.rs`       |     555 |
| `PredictionWfst::minimize()`                  | `prattail/src/wfst.rs`       |     437 |
| `PredictionWfst::prune_by_beam()`             | `prattail/src/wfst.rs`       |     598 |
| `PredictionWfst::normalize_weights()`         | `prattail/src/wfst.rs`       |     624 |
| Pipeline integration (E1 cascade call)        | `prattail/src/pipeline.rs`   |     845 |

**Tests (in `transducer.rs`):**

| Test                                         | What it verifies                              |
|:---------------------------------------------|:----------------------------------------------|
| `test_pass_result_unchanged`                 | `PassResult::unchanged()` has zero changes    |
| `test_pass_result_changed`                   | `PassResult::changed()` carries count+summary |
| `test_dead_state_elimination_not_applicable` | 2-state WFST: pass not applicable             |
| `test_state_minimization_pass`               | Union-created duplicates get merged           |
| `test_beam_pruning_pass`                     | Transitions outside beam are pruned           |
| `test_beam_pruning_infinite_beam`            | Infinite beam: pass not applicable            |
| `test_weight_normalization_pass`             | Best weight becomes 0.0 after normalization   |
| `test_cascade_empty`                         | Empty cascade: 1 iteration, 0 changes         |
| `test_cascade_default_pipeline`              | Default has 3 passes in priority order        |
| `test_cascade_with_beam`                     | with_beam adds 4th pass                       |
| `test_cascade_convergence`                   | Union WFST converges in <= 3 iterations       |
| `test_cascade_run_all`                       | Multi-category run produces summary           |
| `test_cascade_max_iterations`                | Safety bound respected                        |
| `test_cascade_priority_ordering`             | Reverse insertion still yields correct order  |
| `test_cascade_debug_format`                  | Debug output includes all pass names          |

---

## 11. Cross-References

- [Weighted Automata](weighted-automata.md) --
  WFST structure, formal definition, and the prediction pipeline that
  produces the raw WFSTs optimized by this cascade

- [Semirings](semirings.md) --
  weight algebras; in particular, TropicalWeight (used by all four
  built-in passes) and BooleanWeight (the algebraic framework for
  dead-state reachability in T_dead_elim)

- [Grammar Left-Factoring](left-factoring.md) --
  the A1 prefix-sharing optimization; complements the E1 cascade by
  reducing NFA alternatives at the codegen level, whereas E1 optimizes
  the WFST structure at compile time

- [Multi-Token Lookahead](multi-token-lookahead.md) --
  B1 two-token lookahead; another compile-time optimization that
  reduces dispatch ambiguity, independent of E1

- [Token Lattices](token-lattices.md) --
  lattice-based ambiguous tokenization; the prediction WFSTs optimized
  by E1 feed into lattice-aware parsing at runtime

- [Cascade Suppression](cascade-suppression.md) --
  error recovery cascade prevention; a runtime concern orthogonal to
  the compile-time optimization cascade described here

- [Viterbi and Forward-Backward](viterbi-and-forward-backward.md) --
  path-extraction algorithms that operate on the WFSTs after E1
  optimization

---

**References:**

1. **Mohri, M.** (1997). Finite-state transducers in language and
   speech processing. *Computational Linguistics*, 23(2), 269--311.
   Section 5: Composition of weighted transducers. The E1 cascade
   generalizes Mohri's pairwise composition to a sequence of
   endomorphic passes with fixed-point iteration.

2. **Mohri, M., Pereira, F., & Riley, M.** (2002). Weighted
   finite-state transducers in speech recognition. *Computer Speech
   & Language*, 16(1), 69--88. Section 4.2: Optimization of WFST
   cascades in the ASR pipeline (composition, determinization,
   minimization, weight pushing).

3. **Mohri, M.** (2009). Weighted automata algorithms. In *Handbook
   of Weighted Automata* (pp. 213--254). Springer. Chapter 6:
   Minimization of weighted automata. The signature-based equivalence
   used in T_minimize is a simplified instance of Mohri's weighted
   minimization for the non-deterministic case.

4. **Allauzen, C., Riley, M., Schalkwyk, J., Skut, W., & Mohri, M.**
   (2007). OpenFst: A general and efficient weighted finite-state
   transducer library. *Proceedings of CIAA*, 11--23. The OpenFst
   library implements optimization cascades for speech recognition;
   PraTTaIL's E1 follows the same compose-then-iterate pattern
   adapted to parser dispatch optimization.
