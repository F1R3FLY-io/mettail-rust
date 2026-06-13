# RhoNet Scheduler TLA+ Model

This bounded TLA+ model complements the process-calculus and Rocq Rho bridge
proofs. It models three independent RhoNet COMM redexes, `A`, `B`, and `C`,
and a single completion observation `Q`.

The model checks two kinds of facts:

1. Bounded safety with Apalache: traces remain well typed, completion occurs
   only after all three independent inputs, trace observations match scheduler
   state, and completion is enabled once all inputs have fired.
2. Weak-fairness liveness with TLC: if the scheduler is weakly fair for `A`,
   `B`, `C`, and `Complete`, then `<> completed` holds.

This model does not verify the full Rholang interpreter or RSpace
implementation. It is a finite scheduler projection that complements
`formal/mcrl2/rho_machine/`, `formal/maude/rho_machine/`, and the unbounded
Rocq bridge theories.

Run through the repository cap:

```sh
make -C formal check-capped FORMAL_CAPPED_TARGET=tla-rho-machine
```
