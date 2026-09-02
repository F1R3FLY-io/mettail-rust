From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Record Weight : Type := {
  recovery : nat;
  ambiguity : nat;
  preference : nat;
  declaration : nat
}.

Definition zero : Weight :=
  {| recovery := 0; ambiguity := 0; preference := 0; declaration := 0 |}.

Definition extend (left right : Weight) : Weight :=
  {| recovery := recovery left + recovery right;
     ambiguity := ambiguity left + ambiguity right;
     preference := preference left + preference right;
     declaration := declaration left + declaration right |}.

Definition weight_le (left right : Weight) : Prop :=
  recovery left < recovery right \/
  (recovery left = recovery right /\
   (ambiguity left < ambiguity right \/
    (ambiguity left = ambiguity right /\
     (preference left < preference right \/
      (preference left = preference right /\ declaration left <= declaration right))))).

Theorem extend_zero_left : forall weight, extend zero weight = weight.
Proof. intros [r a p d]. reflexivity. Qed.

Theorem extend_zero_right : forall weight, extend weight zero = weight.
Proof. intros [r a p d]. unfold extend, zero. simpl. f_equal; lia. Qed.

Theorem extend_associative :
  forall first second third,
    extend (extend first second) third = extend first (extend second third).
Proof.
  intros [r1 a1 p1 d1] [r2 a2 p2 d2] [r3 a3 p3 d3].
  unfold extend. simpl. f_equal; lia.
Qed.

Theorem extend_commutative : forall left right, extend left right = extend right left.
Proof.
  intros [r1 a1 p1 d1] [r2 a2 p2 d2]. unfold extend. simpl. f_equal; lia.
Qed.

Theorem weight_le_reflexive : forall weight, weight_le weight weight.
Proof.
  intros [r a p d]. unfold weight_le. simpl. right. split; [reflexivity |].
  right. split; [reflexivity |]. right. split; [reflexivity | lia].
Qed.

Theorem weight_le_total : forall left right, weight_le left right \/ weight_le right left.
Proof.
  intros [r1 a1 p1 d1] [r2 a2 p2 d2]. unfold weight_le. simpl.
  destruct (Nat.lt_trichotomy r1 r2) as [H | [H | H]].
  - left. left. exact H.
  - subst r2. destruct (Nat.lt_trichotomy a1 a2) as [H | [H | H]].
    + left. right. split; [reflexivity | left; exact H].
    + subst a2. destruct (Nat.lt_trichotomy p1 p2) as [H | [H | H]].
      * left. right. split; [reflexivity |]. right. split; [reflexivity | left; exact H].
      * subst p2. destruct (Nat.le_ge_cases d1 d2) as [Hd | Hd].
        -- left. right. split; [reflexivity |]. right. split; [reflexivity |].
           right. split; [reflexivity | exact Hd].
        -- right. right. split; [reflexivity |]. right. split; [reflexivity |].
           right. split; [reflexivity | exact Hd].
      * right. right. split; [reflexivity |]. right. split; [reflexivity | left; exact H].
    + right. right. split; [reflexivity | left; exact H].
  - right. left. exact H.
Qed.

Theorem extend_monotone_left :
  forall left right suffix,
    weight_le left right -> weight_le (extend left suffix) (extend right suffix).
Proof.
  intros [lr la lp ld] [rr ra rp rd] [sr sa sp sd] H.
  unfold weight_le, extend in *. simpl in *.
  destruct H as [H | [H [H1 | [H1 [H2 | [H2 H3]]]]]].
  - left. lia.
  - right. split; [lia | left; lia].
  - right. split; [lia | right; split; [lia | left; lia]].
  - right. split; [lia | right; split; [lia | right; split; lia]].
Qed.

Theorem extend_monotone_right :
  forall prefix left right,
    weight_le left right -> weight_le (extend prefix left) (extend prefix right).
Proof.
  intros prefix left right H.
  rewrite (extend_commutative prefix left), (extend_commutative prefix right).
  apply extend_monotone_left. exact H.
Qed.

Fixpoint all_dominated_by (best : Weight) (candidates : list Weight) : Prop :=
  match candidates with
  | [] => True
  | candidate :: rest => weight_le best candidate /\ all_dominated_by best rest
  end.

Theorem extension_preserves_argmin :
  forall best candidates suffix,
    all_dominated_by best candidates ->
    all_dominated_by
      (extend best suffix)
      (map (fun candidate => extend candidate suffix) candidates).
Proof.
  intros best candidates. induction candidates as [| candidate rest IH]; intros suffix H.
  - exact I.
  - simpl in *. destruct H as [Hcandidate Hrest]. split.
    + apply extend_monotone_left. exact Hcandidate.
    + apply IH. exact Hrest.
Qed.

Print Assumptions extend_associative.
Print Assumptions weight_le_total.
Print Assumptions extension_preserves_argmin.
