# Process-Calculus Verification Map

This directory records executable finite projections that complement the
unbounded Rocq Rho bridge proofs.

## Authority Boundary

Rocq remains authoritative for unbounded semantic claims such as lowering
soundness, observation equivalence, artifact-validation gates, name grounding,
the Rust model bridge, and the arity-parametric COMM schedule-family theorem in
`formal/rocq/rho_bridge/theories/RhoCommScheduleFamily.v`. The process-calculus
models here are deliberately finite. They are used for independent
counterexample search and process-level sanity checks over selected RhoNet
fragments.

These finite checks establish that the modeled fragments have the stated
deadlock, schedule-independence, and bisimulation properties. The unbounded
Rocq schedule-family proof establishes the corresponding visible-trace and
premature-completion boundary for every finite list of independent redexes.
Host-level RSpace, full Rholang, Rholang bytecode, and per-language backend
obligations are covered by their own bridge, runtime, and flip-gate suites; this
directory covers the process-level COMM schedule projection and its executable
counterexample-search models.

## Tool Roles

| Tool | Role in this repository |
| --- | --- |
| Rocq | Source-of-truth proofs for unbounded bridge theorems. |
| mCRL2 | Finite process-algebra projections: LTS generation, modal checks, and branching-bisimulation checks. |
| Maude | Executable rewrite-logic projections for reachability and counterexample search. |
| TLA+ | Scheduler and fairness models over bounded state spaces. |
| Isabelle/HOL | Independent nominal-binding and weak-bisimulation metatheory when those claims need a second proof assistant. |

## Current Executable Slice

`rho_comm_slice.json` is the source specification for the current bounded COMM
slice. `rho_comm_slice.py` generates the mCRL2, Maude, and TLA+ model files
from that specification and the formal Makefiles run it in `--check` mode
before invoking the model checkers. This keeps the process-algebra,
rewrite-logic, and scheduler projections tied to the same finite lowering
shape.

`formal/mcrl2/rho_machine/` and `formal/maude/rho_machine/` model a bounded
four-redex RhoNet COMM fragment and the corresponding Dovetail fact-step
fragment. The Rho side includes internal reserve/commit phases; the Dovetail
side exposes direct fact steps. This is an arity-parametric generated
projection, checked here at four independent redexes, not a full
generated-backend proof. The checked properties are:

1. every reachable state has an outgoing transition;
2. all 24 visible fire-order permutations can complete;
3. after any complete visible firing order, completion is enabled;
4. the RhoNet and Dovetail finite projections are branching-bisimilar when
   compared over the same visible fire/complete actions and Rho reserve actions
   are hidden as internal `τ` actions.
5. both rewrite projections have the same unique terminal observation and expose
   every one-step independent redex witness under AC fact-multiset
   normalization;
6. Maude traced configurations realize the same 24 visible fire/complete
   schedules on the RhoNet and Dovetail sides while keeping Rho reserve steps
   unobserved; every visible completion trace with fewer than all four fires is
   unreachable on both sides.

The bounded executable slice is backed by `RhoCommScheduleFamily.v`, which
proves for every finite schedule that Rho reserve steps erase to `τ`, Rho
reserve/fire traces have the same visible observations as direct Dovetail fire
traces, full permutation schedules enable completion, missing-redex prefixes
reject completion, and permutation schedules observe the same fired redex set.

`formal/tla/rho_machine/` models the matching scheduler boundary for the same
four independent redexes. Apalache checks bounded safety invariants, and TLC
checks that weak fairness for `A`, `B`, `C`, `D`, and the completion action
implies eventual completion.
