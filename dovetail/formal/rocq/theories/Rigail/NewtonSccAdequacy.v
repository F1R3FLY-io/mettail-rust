(*
 * NewtonSccAdequacy: the precise boundary between Dovetail's mechanized SCC
 * lowering proof and rigail's Newton-SCC solver contract.
 *
 * Dovetail mechanizes the lowering and the scalar/self-loop closure. The
 * general n-dimensional Newton convergence theorem remains an explicit solver
 * contract here, represented as a proof-carrying record and never as a global
 * axiom. This keeps Print Assumptions clean while making the boundary explicit.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.

From Dovetail.InsideWeights Require Import InsideWeightSccClosure.

Import ListNotations.

Section LinearNewton.

  Context {K : Type} {KA : CommKleeneAlgebra K}.

  Definition linear_newton_solution (a b : K) : K :=
    ktimes (kstar a) b.

  Theorem linear_newton_solution_is_lfp : forall a b,
    is_lfp (fun x => kplus b (ktimes a x)) (linear_newton_solution a b).
  Proof.
    intros a b. unfold linear_newton_solution. apply star_closure_is_lfp.
  Qed.

End LinearNewton.

Section MultiSccContract.

  Context {K : Type}.

  Record SolverContract : Type := {
    system : Type;
    solution : system -> list K;
    satisfies_system : system -> list K -> Prop;
    least_solution : system -> list K -> Prop;
    solver_satisfies : forall s, satisfies_system s (solution s);
    solver_least : forall s, least_solution s (solution s)
  }.

  Definition solver_adequate (sc : SolverContract) (s : system sc) : Prop :=
    satisfies_system sc s (solution sc s) /\ least_solution sc s (solution sc s).

  Theorem contracted_newton_scc_adequate : forall (sc : SolverContract) (s : system sc),
    solver_adequate sc s.
  Proof.
    intros sc s. unfold solver_adequate. split.
    - apply solver_satisfies.
    - apply solver_least.
  Qed.

End MultiSccContract.
