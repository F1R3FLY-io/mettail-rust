(** Consensus for an authored, actionless FLT in a Rholang where guard.

    Every directly reachable normal form is projected through one checked
    guest-to-host Boolean relation. A complete no-match is not a Boolean false:
    it means this normal form has no Boolean answer. Incomplete enumeration and
    conflicting answers are likewise unknown. This is the decision algebra
    used at the service boundary; the kernel and receipt models establish
    which finite roster is complete and authorized. No axioms or admits. *)
From Stdlib Require Import List.
Import ListNotations.

Module DataFreeWhereConsensus.

Inductive Verdict := Yes | No | Unknown.
Inductive ProjectionEvidence :=
  | ProjectedTrue | ProjectedFalse | ExhaustiveNoMatch | Incomplete.

Definition classify e := match e with
  | ProjectedTrue => Yes
  | ProjectedFalse => No
  | ExhaustiveNoMatch | Incomplete => Unknown
  end.

Definition join a b := match a, b with
  | Yes, Yes => Yes
  | No, No => No
  | _, _ => Unknown
  end.

Definition decide (proofs : list ProjectionEvidence) : Verdict :=
  match map classify proofs with
  | [] => Unknown
  | first :: rest => fold_left join rest first
  end.

Lemma join_yes_only : forall a b, join a b = Yes -> a = Yes /\ b = Yes.
Proof. destruct a, b; simpl; intros H; try discriminate; auto. Qed.

Lemma join_no_only : forall a b, join a b = No -> a = No /\ b = No.
Proof. destruct a, b; simpl; intros H; try discriminate; auto. Qed.

Lemma fold_yes_only : forall xs acc,
  fold_left join xs acc = Yes -> acc = Yes /\ Forall (eq Yes) xs.
Proof.
  induction xs as [|x xs IH]; intros acc H.
  - simpl in H. split; [assumption | constructor].
  - simpl in H. destruct (IH (join acc x) H) as [Hjoin Hrest].
    destruct (join_yes_only acc x Hjoin) as [Ha Hx].
    split; [assumption | rewrite Hx; constructor; [reflexivity | assumption]].
Qed.

Lemma fold_no_only : forall xs acc,
  fold_left join xs acc = No -> acc = No /\ Forall (eq No) xs.
Proof.
  induction xs as [|x xs IH]; intros acc H.
  - simpl in H. split; [assumption | constructor].
  - simpl in H. destruct (IH (join acc x) H) as [Hjoin Hrest].
    destruct (join_no_only acc x Hjoin) as [Ha Hx].
    split; [assumption | rewrite Hx; constructor; [reflexivity | assumption]].
Qed.

Theorem yes_requires_every_complete_true_proof : forall proofs,
  decide proofs = Yes -> proofs <> [] /\ Forall (eq ProjectedTrue) proofs.
Proof.
  intros [|first rest] H; simpl in H; try discriminate.
  destruct (fold_yes_only (map classify rest) (classify first) H)
    as [Hfirst Hrest].
  split; [discriminate |].
  constructor.
  - destruct first; simpl in Hfirst; congruence.
  - clear first Hfirst H.
    induction rest as [|x xs IH]; simpl in *; constructor.
    + inversion Hrest; subst. destruct x; simpl in *; congruence.
    + inversion Hrest; subst. apply IH. assumption.
Qed.

Theorem no_requires_every_complete_false_proof : forall proofs,
  decide proofs = No -> proofs <> [] /\ Forall (eq ProjectedFalse) proofs.
Proof.
  intros [|first rest] H; simpl in H; try discriminate.
  destruct (fold_no_only (map classify rest) (classify first) H)
    as [Hfirst Hrest].
  split; [discriminate |].
  constructor.
  - destruct first; simpl in Hfirst; congruence.
  - clear first Hfirst H.
    induction rest as [|x xs IH]; simpl in *; constructor.
    + inversion Hrest; subst. destruct x; simpl in *; congruence.
    + inversion Hrest; subst. apply IH. assumption.
Qed.

Theorem no_match_is_not_false : decide [ExhaustiveNoMatch] = Unknown.
Proof. reflexivity. Qed.

Theorem incomplete_is_not_false : decide [Incomplete] = Unknown.
Proof. reflexivity. Qed.

Theorem a_later_conflict_rejects_an_early_yes :
  decide [ProjectedTrue] = Yes /\
  decide [ProjectedTrue; ProjectedFalse] = Unknown.
Proof. split; reflexivity. Qed.

End DataFreeWhereConsensus.

Print Assumptions DataFreeWhereConsensus.yes_requires_every_complete_true_proof.
Print Assumptions DataFreeWhereConsensus.no_requires_every_complete_false_proof.
Print Assumptions DataFreeWhereConsensus.no_match_is_not_false.
Print Assumptions DataFreeWhereConsensus.incomplete_is_not_false.
Print Assumptions DataFreeWhereConsensus.a_later_conflict_rejects_an_early_yes.
