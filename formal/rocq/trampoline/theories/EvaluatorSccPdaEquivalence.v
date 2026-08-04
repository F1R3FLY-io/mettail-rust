(*
 * EvaluatorSccPdaEquivalence
 *
 * A concrete, zero-admission simulation proof for the generated native
 * evaluator's mutually recursive SCC transform.  The indexed source language
 * contains the two constructor shapes that make category-local trampolines
 * unsound: Int -> Bool and Bool -> Int.  It also contains failure, matching
 * try_eval's None path.
 *
 * Rust traceability (macros/src/gen/native/eval.rs):
 *
 *   eval                         recursive semantic oracle
 *   Visit / ReduceFromBool       VisitInt/VisitBool + ReduceIntBoolToInt
 *   ReduceEqInt                  ReduceBoolEqInt
 *   Running.work                 Vec<__EvalFrameC*>
 *   Running.values               Vec<__EvalValueC*>
 *   Failed                       early return None
 *
 * The theorem is continuation-parametric: arbitrary pending work and values
 * are preserved.  This is the property needed to compose constructor proofs
 * inside one heterogeneous SCC machine, not merely equality at an empty root.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Import ListNotations.

Inductive category : Type := CInt | CBool.

Definition native (c : category) : Type :=
  match c with
  | CInt => nat
  | CBool => bool
  end.

Inductive term : category -> Type :=
  | IntLit : nat -> term CInt
  | IntFromBool : term CBool -> term CInt
  | BoolLit : bool -> term CBool
  | BoolEqInt : term CInt -> term CInt -> term CBool
  | Unevaluable : forall c, term c.

Fixpoint eval {c : category} (t : term c) : option (native c) :=
  match t in term c0 return option (native c0) with
  | IntLit n => Some n
  | IntFromBool b =>
      match eval b with
      | Some true => Some 1
      | Some false => Some 0
      | None => None
      end
  | BoolLit b => Some b
  | BoolEqInt lhs rhs =>
      match eval lhs, eval rhs with
      | Some l, Some r => Some (Nat.eqb l r)
      | _, _ => None
      end
  | Unevaluable _ => None
  end.

Inductive value : Type :=
  | VInt : nat -> value
  | VBool : bool -> value.

Definition value_of (c : category) : native c -> value :=
  match c return native c -> value with
  | CInt => VInt
  | CBool => VBool
  end.

Inductive task : Type :=
  | Visit : forall c, term c -> task
  | ReduceFromBool
  | ReduceEqInt.

Inductive state : Type :=
  | Running : list task -> list value -> state
  | Failed : state.

Definition finish (c : category) (result : option (native c))
    (work : list task) (values : list value) : state :=
  match result with
  | Some result => Running work (value_of c result :: values)
  | None => Failed
  end.

Inductive step : state -> state -> Prop :=
  | StepIntLit : forall n work values,
      step (Running (Visit CInt (IntLit n) :: work) values)
           (Running work (VInt n :: values))
  | StepIntFromBool : forall child work values,
      step (Running (Visit CInt (IntFromBool child) :: work) values)
           (Running (Visit CBool child :: ReduceFromBool :: work) values)
  | StepBoolLit : forall b work values,
      step (Running (Visit CBool (BoolLit b) :: work) values)
           (Running work (VBool b :: values))
  | StepBoolEqInt : forall lhs rhs work values,
      step (Running (Visit CBool (BoolEqInt lhs rhs) :: work) values)
           (Running
              (Visit CInt lhs :: Visit CInt rhs :: ReduceEqInt :: work)
              values)
  | StepUnevaluable : forall c work values,
      step (Running (Visit c (Unevaluable c) :: work) values) Failed
  | StepReduceFromBool : forall b work values,
      step (Running (ReduceFromBool :: work) (VBool b :: values))
           (Running work (VInt (if b then 1 else 0) :: values))
  | StepReduceEqInt : forall rhs lhs work values,
      step (Running (ReduceEqInt :: work) (VInt rhs :: VInt lhs :: values))
           (Running work (VBool (Nat.eqb lhs rhs) :: values)).

Inductive steps : state -> state -> Prop :=
  | StepsRefl : forall s, steps s s
  | StepsCons : forall s1 s2 s3, step s1 s2 -> steps s2 s3 -> steps s1 s3.

Lemma steps_trans : forall s1 s2 s3, steps s1 s2 -> steps s2 s3 -> steps s1 s3.
Proof.
  intros s1 s2 s3 H12 H23.
  induction H12.
  - exact H23.
  - eapply StepsCons; eauto.
Qed.

Theorem evaluator_scc_pda_equivalence :
  forall c (t : term c) work values,
    steps (Running (Visit c t :: work) values)
          (finish c (eval t) work values).
Proof.
  intros c t.
  induction t as [n | child IH | b | lhs IHlhs rhs IHrhs | c].
  - intros work values. simpl.
    eapply StepsCons. constructor. constructor.
  - intros work values. simpl.
    eapply steps_trans.
    + eapply StepsCons. constructor. constructor.
    + specialize (IH (ReduceFromBool :: work) values).
      destruct (eval child) as [child_value |] eqn:Heval.
      * destruct child_value.
        -- eapply steps_trans. exact IH.
           eapply StepsCons. constructor. constructor.
        -- eapply steps_trans. exact IH.
           eapply StepsCons. constructor. constructor.
      * exact IH.
  - intros work values. simpl.
    eapply StepsCons. constructor. constructor.
  - intros work values. simpl.
    eapply steps_trans.
    + eapply StepsCons. constructor. constructor.
    + specialize
        (IHlhs (Visit CInt rhs :: ReduceEqInt :: work) values).
      destruct (eval lhs) as [lhs_value |] eqn:Hlhs.
      * simpl in IHlhs.
        eapply steps_trans. exact IHlhs.
        specialize (IHrhs (ReduceEqInt :: work) (VInt lhs_value :: values)).
        destruct (eval rhs) as [rhs_value |] eqn:Hrhs.
        -- simpl in IHrhs.
           eapply steps_trans. exact IHrhs.
           eapply StepsCons. constructor. constructor.
        -- exact IHrhs.
      * exact IHlhs.
  - intros work values. simpl.
    eapply StepsCons. constructor. constructor.
Qed.

Corollary evaluator_scc_pda_root_result :
  forall c (t : term c),
    steps (Running [Visit c t] []) (finish c (eval t) [] []).
Proof.
  intros. apply evaluator_scc_pda_equivalence.
Qed.
