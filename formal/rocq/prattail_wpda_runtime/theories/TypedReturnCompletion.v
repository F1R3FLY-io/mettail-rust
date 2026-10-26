(* A Return-frame Pratt continuation may finish its binary RHS before an
   operator whose every certified outcome is foreign to that RHS.  The
   completed rule then offers the operator to its caller at the saved floor.
   This model is deliberately conditional: mixed RHS/outer overloads require
   candidate-specific continuation, not an unrestricted early pop. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.

Section TypedReturnCompletion.
  Variable reaches : nat -> nat -> bool.

  Record Site := {
    pending_binary_return : bool;
    completed_rhs_admitted : bool;
    outer_operator_admitted : bool;
    rhs_expected : list nat;
    candidate_outcomes : list nat;
  }.

  Definition candidate_compatible (s : Site) (candidate : nat) : bool :=
    existsb (reaches candidate) (rhs_expected s).

  Definition all_foreign (s : Site) : bool :=
    match candidate_outcomes s with
    | [] => false
    | cs => forallb (fun c => negb (candidate_compatible s c)) cs
    end.

  Definition offer_completion (s : Site) : bool :=
    pending_binary_return s && completed_rhs_admitted s &&
    outer_operator_admitted s && all_foreign s.

  Inductive Reading := Existing (candidate : nat) | Complete.

  Definition dispatch (s : Site) : list Reading :=
    map Existing (candidate_outcomes s) ++
    if offer_completion s then [Complete] else [].

  Theorem existing_candidates_preserved :
    forall s c, In c (candidate_outcomes s) -> In (Existing c) (dispatch s).
  Proof.
    intros s c H. unfold dispatch. apply in_or_app. left.
    apply in_map. exact H.
  Qed.

  Theorem completion_only_when_typed_and_outer_admitted :
    forall s, In Complete (dispatch s) ->
      pending_binary_return s = true /\
      completed_rhs_admitted s = true /\
      outer_operator_admitted s = true /\
      candidate_outcomes s <> [] /\
      forall c, In c (candidate_outcomes s) -> candidate_compatible s c = false.
  Proof.
    intros s H.
    unfold dispatch in H. apply in_app_or in H.
    destruct H as [H | H].
    - apply in_map_iff in H. destruct H as [c [H _]]. discriminate H.
    - destruct (offer_completion s) eqn:Ho; simpl in H;
        [| contradiction].
      unfold offer_completion in Ho.
      repeat rewrite andb_true_iff in Ho.
      destruct Ho as [[[Hr Hb] Houter] Hforeign].
      repeat split; try assumption.
      unfold all_foreign in Hforeign.
      + destruct (candidate_outcomes s) as [|c cs] eqn:Hcs;
          simpl in Hforeign; try discriminate.
      + intros c Hin.
        unfold all_foreign in Hforeign.
        destruct (candidate_outcomes s) as [|c0 cs] eqn:Hcs;
          [discriminate Hforeign|].
        pose proof (proj1 (forallb_forall
          (fun x => negb (candidate_compatible s x)) (c0 :: cs))
          Hforeign c Hin) as Hc.
        apply negb_true_iff in Hc. exact Hc.
  Qed.

  Theorem rhs_compatible_candidate_blocks_unrestricted_completion :
    forall s c, In c (candidate_outcomes s) ->
      candidate_compatible s c = true -> ~ In Complete (dispatch s).
  Proof.
    intros s c Hin Hreach Hcomplete.
    pose proof (completion_only_when_typed_and_outer_admitted s Hcomplete)
      as [_ [_ [_ [_ Hforeign]]]].
    pose proof (Hforeign c Hin) as Hfalse.
    rewrite Hreach in Hfalse. discriminate.
  Qed.

  Theorem foreign_candidates_offer_completion :
    forall s, pending_binary_return s = true ->
      completed_rhs_admitted s = true ->
      outer_operator_admitted s = true ->
      candidate_outcomes s <> [] ->
      (forall c, In c (candidate_outcomes s) ->
        candidate_compatible s c = false) ->
      In Complete (dispatch s).
  Proof.
    intros s Hr Hb Ho Hnonempty Hforeign.
    unfold dispatch. apply in_or_app. right.
    assert (Hall : all_foreign s = true).
    { unfold all_foreign.
      destruct (candidate_outcomes s) as [|c cs] eqn:Hcs.
      - contradiction.
      - apply forallb_forall. intros x Hx.
        apply negb_true_iff. apply Hforeign. exact Hx. }
    unfold offer_completion. rewrite Hr, Hb, Ho, Hall. simpl. auto.
  Qed.

  (* The extra edge is epsilon; the original candidates retain their
     consumption and semiring weights.  The concrete walker uses the same
     descriptor and its existing Return pop/GSS-SPPF replay. *)
  Definition position_after (pos : nat) (r : Reading) : nat :=
    match r with Existing _ => S pos | Complete => pos end.

  Theorem completion_consumes_no_input :
    forall pos, position_after pos Complete = pos.
  Proof. reflexivity. Qed.
End TypedReturnCompletion.

Print Assumptions existing_candidates_preserved.
Print Assumptions completion_only_when_typed_and_outer_admitted.
Print Assumptions rhs_compatible_candidate_blocks_unrestricted_completion.
Print Assumptions foreign_candidates_offer_completion.
Print Assumptions completion_consumes_no_input.
