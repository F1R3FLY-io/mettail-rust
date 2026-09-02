From Stdlib Require Import List PeanoNat.
Import ListNotations.

Definition NodeKey := nat.
Definition Alternative := nat.
Definition Forest := list (NodeKey * list Alternative).

Fixpoint alternatives (key : NodeKey) (forest : Forest) : list Alternative :=
  match forest with
  | [] => []
  | (candidate, packed) :: rest =>
      if Nat.eqb key candidate then packed else alternatives key rest
  end.

Definition insert_alternative (alternative : Alternative) (packed : list Alternative)
  : list Alternative :=
  if existsb (Nat.eqb alternative) packed then packed else alternative :: packed.

Fixpoint intern (key : NodeKey) (alternative : Alternative) (forest : Forest) : Forest :=
  match forest with
  | [] => [(key, [alternative])]
  | (candidate, packed) :: rest =>
      if Nat.eqb key candidate
      then (candidate, insert_alternative alternative packed) :: rest
      else (candidate, packed) :: intern key alternative rest
  end.

Lemma insert_alternative_contains_new :
  forall alternative packed, In alternative (insert_alternative alternative packed).
Proof.
  intros alternative packed. unfold insert_alternative.
  destruct (existsb (Nat.eqb alternative) packed) eqn:Hexists.
  - apply existsb_exists in Hexists. destruct Hexists as [value [Hin Heq]].
    apply Nat.eqb_eq in Heq. subst value. exact Hin.
  - left. reflexivity.
Qed.

Lemma insert_alternative_preserves_old :
  forall alternative old packed,
    In old packed -> In old (insert_alternative alternative packed).
Proof.
  intros alternative old packed Hin. unfold insert_alternative.
  destruct (existsb (Nat.eqb alternative) packed); [exact Hin | right; exact Hin].
Qed.

Theorem intern_contains_new :
  forall key alternative forest,
    In alternative (alternatives key (intern key alternative forest)).
Proof.
  intros key alternative forest. induction forest as [| [candidate packed] rest IH].
  - simpl. rewrite Nat.eqb_refl. left. reflexivity.
  - simpl. destruct (Nat.eqb key candidate) eqn:Heq.
    + simpl. rewrite Heq. apply insert_alternative_contains_new.
    + simpl. rewrite Heq. exact IH.
Qed.

Theorem intern_preserves_same_key :
  forall key alternative old forest,
    In old (alternatives key forest) ->
    In old (alternatives key (intern key alternative forest)).
Proof.
  intros key alternative old forest. induction forest as [| [candidate packed] rest IH]; intro Hin.
  - contradiction.
  - simpl in Hin. simpl. destruct (Nat.eqb key candidate) eqn:Heq.
    + simpl. rewrite Heq. apply insert_alternative_preserves_old. exact Hin.
    + simpl. rewrite Heq. apply IH. exact Hin.
Qed.

Theorem intern_preserves_other_key :
  forall key other alternative forest,
    key <> other ->
    alternatives other (intern key alternative forest) = alternatives other forest.
Proof.
  intros key other alternative forest Hneq. induction forest as [| [candidate packed] rest IH].
  - simpl. destruct (Nat.eqb other key) eqn:Heq.
    + apply Nat.eqb_eq in Heq. exfalso. apply Hneq. symmetry. exact Heq.
    + reflexivity.
  - simpl. destruct (Nat.eqb key candidate) eqn:Hkey.
    + apply Nat.eqb_eq in Hkey. subst candidate. simpl.
      destruct (Nat.eqb other key) eqn:Hother.
      * apply Nat.eqb_eq in Hother. exfalso. apply Hneq. symmetry. exact Hother.
      * reflexivity.
    + simpl. destruct (Nat.eqb other candidate); [reflexivity | exact IH].
Qed.

Definition denotes (forest : Forest) (key : NodeKey) (alternative : Alternative) : Prop :=
  In alternative (alternatives key forest).

Theorem hash_consing_is_monotone :
  forall forest key alternative observed_key observed_alternative,
    denotes forest observed_key observed_alternative ->
    denotes (intern key alternative forest) observed_key observed_alternative.
Proof.
  intros forest key alternative observed_key observed_alternative Hdenotes.
  destruct (Nat.eq_dec key observed_key) as [Heq | Hneq].
  - subst observed_key. apply intern_preserves_same_key. exact Hdenotes.
  - unfold denotes in *. rewrite intern_preserves_other_key; assumption.
Qed.

Print Assumptions intern_contains_new.
Print Assumptions hash_consing_is_monotone.
