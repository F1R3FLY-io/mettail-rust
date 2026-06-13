# Process-Calculus Verification Map

This directory records executable finite projections that complement the
unbounded Rocq Rho bridge proofs.

## Authority Boundary

Rocq remains authoritative for unbounded semantic claims such as lowering
soundness, observation equivalence, artifact-validation gates, name grounding,
and the Rust model bridge. The process-calculus models here are deliberately
finite. They are used for independent counterexample search and process-level
sanity checks over selected RhoNet fragments.

These finite checks establish that the modeled fragments have the stated
deadlock, schedule-independence, and bisimulation properties. They do not, by
themselves, verify the full f1r3node RSpace implementation, the full Rholang
language, Rholang bytecode, or every MeTTaIL language backend.

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

`formal/tla/rho_machine/` models the matching scheduler boundary for the same
four independent redexes. Apalache checks bounded safety invariants, and TLC
checks that weak fairness for `A`, `B`, `C`, `D`, and the completion action
implies eventual completion.
