(*
 * CohortQuotient: proof obligations for DispatchKey -> EquivKey.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From PrattailWpdaRuntime Require Import RuntimeModel.

Import ListNotations.

Definition with_cohort_origin (base : config_key) (d : dispatch_key) : config_key :=
  {| ck_control := ck_control base;
     ck_node := ck_node base;
     ck_pos := ck_pos base;
     ck_incoming_edge := ck_incoming_edge base;
     ck_collection_depth := ck_collection_depth base;
     ck_origin := Some (equiv_of_dispatch d);
     ck_sppf_top := ck_sppf_top base;
     ck_lex_alt := ck_lex_alt base;
     ck_weight_src := ck_weight_src base;
     ck_weight_rule := ck_weight_rule base;
     ck_lex_stamp := ck_lex_stamp base |}.

Lemma dispatch_keys_with_same_source_bp_share_origin :
  forall base p1 p2 s bp wc1 wr1 wc2 wr2,
    with_cohort_origin base
      {| dk_pos := p1; dk_source := s; dk_bp := bp;
         dk_wrap_cat := wc1; dk_wrap_rule := wr1 |}
    =
    with_cohort_origin base
      {| dk_pos := p2; dk_source := s; dk_bp := bp;
         dk_wrap_cat := wc2; dk_wrap_rule := wr2 |}.
Proof. reflexivity. Qed.

Lemma different_sppf_tops_prevent_merge :
  forall c1 c2,
    ck_sppf_top (observable c1) <> ck_sppf_top (observable c2) ->
    observable c1 <> observable c2.
Proof.
  intros c1 c2 Hdiff Heq.
  apply Hdiff.
  now rewrite Heq.
Qed.

Lemma different_lex_stamps_prevent_merge :
  forall c1 c2,
    ck_lex_stamp (observable c1) <> ck_lex_stamp (observable c2) ->
    observable c1 <> observable c2.
Proof.
  intros c1 c2 Hdiff Heq.
  apply Hdiff.
  now rewrite Heq.
Qed.

Theorem cohort_quotient_step_sound :
  forall (step : cursor -> list cursor) c1 c2,
    config_deterministic step ->
    origin_consistent c1 ->
    origin_consistent c2 ->
    observable c1 = observable c2 ->
    map observable (step c1) = map observable (step c2).
Proof.
  intros step c1 c2 Hdet Hc1 Hc2 Hobs.
  eapply quotient_step_sound; eauto.
Qed.

Theorem merge_preserves_observable_set :
  forall cs k,
    In k (config_keys cs) <->
    exists c, In c cs /\ observable c = k.
Proof.
  apply config_keys_spec.
Qed.

Theorem merge_observable_count_bounded :
  forall cs,
    length (config_keys cs) <= length cs.
Proof.
  apply config_keys_length_le.
Qed.
