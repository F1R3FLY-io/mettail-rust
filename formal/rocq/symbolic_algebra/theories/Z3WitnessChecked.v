(*
 * Z3WitnessChecked: the certificate-check discipline that keeps the Z3/SMT oracle
 * (OSLF Phase 8, prattail/src/logict_smt.rs) SOUND without admitting it into the
 * proven EBA core.
 *
 * The Z3 backend is exposed ONLY via a three-valued `is_satisfiable_3v -> Sat3`
 * (unknown -> Sat3::DontKnow, never a silent false) and a `checked_witness` that
 * re-validates every model `m` under the PURE evaluator `eval_constraint(c, m)`
 * before returning it. This file certifies that the certificate check is SOUND BY
 * CONSTRUCTION — a returned checked witness implies the constraint is satisfiable,
 * and genuinely evaluates it true — INDEPENDENT of the solver. So a trusted Z3
 * `Sat` is backed by a re-checkable certificate; no Z3 result is taken on faith,
 * and NO new admission enters `EffectiveBooleanAlgebra.v` (the oracle lives
 * entirely in Rust behind the Sat3 channel).
 *
 * This is the formal image of `logict_smt::checked_witness` (returns `Some m`
 * only when `eval_constraint(c, m)` re-confirms) + the `GuardTierCertificate.v`
 * T3/T4 discipline (Z3-with-a-definite-answer is T3 Boundary; Z3 `unknown`
 * degrades to T4). It is abstract over the constraint/model/evaluator, so it
 * applies to the concrete SmtConstraint/SmtModel/eval_constraint unchanged.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

Section Z3WitnessChecked.
  (* A constraint language, a model space, and a PURE boolean evaluator (the Rust
     `eval_constraint` / `eval_term`). Section variables are discharged on `End`,
     so the results below are fully general and axiom-free. *)
  Context {Constraint Model : Type}.
  Variable eval : Constraint -> Model -> bool.

  (* Satisfiability = some model evaluates the constraint true. *)
  Definition sat (c : Constraint) : Prop := exists m, eval c m = true.

  (* The certificate-checked witness: a candidate model is RETURNED only when the
     pure evaluator re-confirms it (mirrors `checked_witness`, which re-runs
     `eval_constraint` before trusting Z3's model). *)
  Definition checked_witness (c : Constraint) (candidate : option Model) : option Model :=
    match candidate with
    | Some m => if eval c m then Some m else None
    | None => None
    end.

  (* Soundness by construction: a returned checked witness implies satisfiable —
     so a trusted Z3 `Sat` is always certificate-backed, never taken on faith. *)
  Theorem checked_witness_sound : forall c candidate m,
    checked_witness c candidate = Some m -> sat c.
  Proof.
    intros c candidate m H. unfold checked_witness in H.
    destruct candidate as [m0 |]; [ | discriminate ].
    destruct (eval c m0) eqn:E; [ | discriminate ].
    exists m0. exact E.
  Qed.

  (* The returned witness genuinely evaluates the constraint true (the certificate
     itself is valid). *)
  Theorem checked_witness_evaluates : forall c candidate m,
    checked_witness c candidate = Some m -> eval c m = true.
  Proof.
    intros c candidate m H. unfold checked_witness in H.
    destruct candidate as [m0 |]; [ | discriminate ].
    destruct (eval c m0) eqn:E; [ | discriminate ].
    injection H as H. subst m0. exact E.
  Qed.

  (* The check never invents a witness: `None` in yields `None` out (an unknown /
     unsat Z3 answer is never upgraded to a fabricated Sat). *)
  Theorem checked_witness_no_fabrication : forall c,
    checked_witness c None = None.
  Proof. reflexivity. Qed.

End Z3WitnessChecked.

Print Assumptions checked_witness_sound.
Print Assumptions checked_witness_evaluates.
Print Assumptions checked_witness_no_fabrication.
