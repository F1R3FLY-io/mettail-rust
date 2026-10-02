(** A reservation-aware refinement of longest-per-kind lattice selection.

    A DFA state carries [shadow = true] exactly when keyword reservation
    removed an equal-span Ident co-accept from its primary token. Only a
    shorter Ident candidate may be removed. In particular, unrelated custom
    literal candidates are never pruned, even when written adjacently.
    The witness construction and its preservation through DFA minimization
    are implementation obligations; this file proves the survivor filter's
    consequences given that witness. *)
From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Record Candidate := {
  candidate_kind : nat;
  candidate_end : nat
}.

Definition ident_kind := 0.

Definition keep (primary_end : nat) (shadow : bool) (entry : Candidate) : bool :=
  negb (shadow && Nat.eqb (candidate_kind entry) ident_kind
               && Nat.ltb (candidate_end entry) primary_end).

Definition survivors (primary_end : nat) (shadow : bool)
    (entries : list Candidate) : list Candidate :=
  filter (keep primary_end shadow) entries.

Theorem no_witness_is_identity : forall limit entries,
  survivors limit false entries = entries.
Proof.
  intros limit entries. unfold survivors.
  induction entries as [|entry rest IH]; cbn; auto.
  now rewrite IH.
Qed.

Theorem every_survivor_was_a_candidate : forall limit shadow entries entry,
  In entry (survivors limit shadow entries) -> In entry entries.
Proof.
  intros limit shadow entries entry Hin.
  unfold survivors in Hin. apply filter_In in Hin. exact (proj1 Hin).
Qed.

Theorem only_shorter_ident_is_removed : forall limit shadow entries entry,
  In entry entries -> ~ In entry (survivors limit shadow entries) ->
  shadow = true /\ candidate_kind entry = ident_kind /\ candidate_end entry < limit.
Proof.
  intros limit shadow entries entry Hin Hout.
  destruct shadow.
  - assert (Hkeep : keep limit true entry = false).
    { destruct (keep limit true entry) eqn:H; [exfalso|reflexivity].
      apply Hout. unfold survivors. apply filter_In. auto. }
    unfold keep in Hkeep. cbn in Hkeep.
    apply Bool.negb_false_iff in Hkeep.
    apply Bool.andb_true_iff in Hkeep as [Hkind Hlt].
    apply Nat.eqb_eq in Hkind. apply Nat.ltb_lt in Hlt.
    auto.
  - rewrite no_witness_is_identity in Hout. contradiction.
Qed.

Theorem custom_literal_survives : forall limit shadow entries entry,
  candidate_kind entry <> ident_kind -> In entry entries ->
  In entry (survivors limit shadow entries).
Proof.
  intros limit shadow entries entry Hkind Hin.
  unfold survivors. apply filter_In. split; [exact Hin|].
  unfold keep. destruct shadow; cbn; [|reflexivity].
  apply Nat.eqb_neq in Hkind. now rewrite Hkind.
Qed.

Theorem full_span_survives : forall limit shadow entries entry,
  candidate_end entry = limit -> In entry entries ->
  In entry (survivors limit shadow entries).
Proof.
  intros limit shadow entries entry Hend Hin.
  unfold survivors. apply filter_In. split; [exact Hin|].
  unfold keep. rewrite Hend, Nat.ltb_irrefl. now rewrite Bool.andb_false_r.
Qed.

Theorem witnessed_survivor_has_no_short_ident : forall limit entries entry,
  In entry (survivors limit true entries) ->
  candidate_kind entry = ident_kind -> limit <= candidate_end entry.
Proof.
  intros limit entries entry Hin Hkind.
  unfold survivors in Hin. apply filter_In in Hin as [_ Hkeep].
  unfold keep in Hkeep. rewrite Hkind, Nat.eqb_refl in Hkeep.
  cbn in Hkeep. apply Bool.negb_true_iff in Hkeep.
  apply Nat.ltb_ge in Hkeep. exact Hkeep.
Qed.
