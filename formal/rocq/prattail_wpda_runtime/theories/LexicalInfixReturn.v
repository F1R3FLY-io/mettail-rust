From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Module LexicalInfixReturn.

Section Dispatch.
Context {Operator : Type}.

Inductive branch :=
| Continue : Operator -> branch
| Return : nat -> nat -> branch.

Definition dispatch source position structural
    (primary secondary : list Operator) : list branch :=
  map Continue primary ++
  (if (match primary with [] => true | _ => false end) || structural
   then [Return source position] else []) ++
  map Continue secondary.

Fixpoint operators (branches : list branch) : list Operator :=
  match branches with
  | [] => []
  | Continue op :: rest => op :: operators rest
  | Return _ _ :: rest => operators rest
  end.

Fixpoint returns (branches : list branch) : list (nat * nat) :=
  match branches with
  | [] => []
  | Continue _ :: rest => returns rest
  | Return source position :: rest => (source, position) :: returns rest
  end.

Lemma operators_append : forall a b,
  operators (a ++ b) = operators a ++ operators b.
Proof. induction a as [|[op|source position] rest IH]; intros; simpl; congruence. Qed.

Lemma returns_append : forall a b,
  returns (a ++ b) = returns a ++ returns b.
Proof. induction a as [|[op|source position] rest IH]; intros; simpl; congruence. Qed.

Lemma operators_map : forall ops, operators (map Continue ops) = ops.
Proof. induction ops; simpl; congruence. Qed.

Lemma returns_map : forall ops, returns (map Continue ops) = [].
Proof. induction ops; simpl; congruence. Qed.

Theorem operator_branches_are_unchanged : forall source position structural primary secondary,
  operators (dispatch source position structural primary secondary) = primary ++ secondary.
Proof.
  intros. unfold dispatch. rewrite !operators_append, !operators_map.
  destruct primary; destruct structural; simpl; reflexivity.
Qed.

Theorem return_branch_is_exact : forall source position structural primary secondary,
  returns (dispatch source position structural primary secondary) =
  if (match primary with [] => true | _ => false end) || structural
  then [(source, position)] else [].
Proof.
  intros. unfold dispatch. rewrite !returns_append, !returns_map.
  destruct primary; destruct structural; simpl; reflexivity.
Qed.

Theorem nonoperator_primary_keeps_return : forall source position structural secondary,
  returns (dispatch source position structural [] secondary) = [(source, position)].
Proof. intros. rewrite return_branch_is_exact. reflexivity. Qed.

Theorem admitted_primary_keeps_precedence : forall source position first rest secondary,
  returns (dispatch source position false (first :: rest) secondary) = [].
Proof. intros. rewrite return_branch_is_exact. reflexivity. Qed.

Theorem structural_return_remains_available : forall source position primary secondary,
  returns (dispatch source position true primary secondary) = [(source, position)].
Proof. intros. rewrite return_branch_is_exact. destruct primary; reflexivity. Qed.

Theorem at_most_one_return : forall source position structural primary secondary,
  length (returns (dispatch source position structural primary secondary)) <= 1.
Proof.
  intros. rewrite return_branch_is_exact. destruct primary; destruct structural; simpl; lia.
Qed.

Theorem return_preserves_source_and_position :
  forall source position structural primary secondary returned_source returned_position,
  In (returned_source, returned_position)
    (returns (dispatch source position structural primary secondary)) ->
  returned_source = source /\ returned_position = position.
Proof.
  intros. rewrite return_branch_is_exact in H.
  destruct primary; destruct structural; simpl in H;
    try contradiction; destruct H as [H | H]; try contradiction;
    inversion H; auto.
Qed.

Theorem operator_membership_is_exact : forall source position structural primary secondary op,
  In op (operators (dispatch source position structural primary secondary)) <->
  In op primary \/ In op secondary.
Proof. intros. rewrite operator_branches_are_unchanged, in_app_iff. reflexivity. Qed.

End Dispatch.

Example missing_primary_return_counterexample :
  returns (map (@Continue nat) [7]) = [] /\
  returns (dispatch 2 19 false [] [7]) = [(2, 19)].
Proof. split; reflexivity. Qed.

Print Assumptions operator_branches_are_unchanged.
Print Assumptions return_branch_is_exact.
Print Assumptions nonoperator_primary_keeps_return.
Print Assumptions admitted_primary_keeps_precedence.
Print Assumptions structural_return_remains_available.
Print Assumptions at_most_one_return.
Print Assumptions return_preserves_source_and_position.
Print Assumptions operator_membership_is_exact.
Print Assumptions missing_primary_return_counterexample.

End LexicalInfixReturn.
