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
     ck_incoming_edge_stack := ck_incoming_edge_stack base;
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

Lemma different_incoming_edge_stacks_prevent_merge :
  forall c1 c2,
    ck_incoming_edge_stack (observable c1) <>
      ck_incoming_edge_stack (observable c2) ->
    observable c1 <> observable c2.
Proof.
  intros c1 c2 Hdiff Heq.
  apply Hdiff.
  now rewrite Heq.
Qed.

Record cohort_shell_model : Type := {
  csm_config : config_key;
  csm_representative_incoming_edge_stack : nat
}.

Record cohort_member_model : Type := {
  cmm_incoming_edge_stack : nat;
  cmm_origin : option dispatch_key;
  cmm_weight : nat
}.

Definition materialize_cohort_member
    (shell : cohort_shell_model)
    (member : cohort_member_model) : cursor :=
  {| cur_config :=
       config_with_incoming_edge_stack
         (csm_config shell)
         (cmm_incoming_edge_stack member);
     cur_origin := cmm_origin member;
     cur_weight := cmm_weight member |}.

Theorem cohort_materialize_restores_member_incoming_edge_stack :
  forall shell member,
    ck_incoming_edge_stack
      (observable (materialize_cohort_member shell member)) =
    cmm_incoming_edge_stack member.
Proof. reflexivity. Qed.

Theorem cohort_materialize_does_not_use_shell_representative_stack :
  forall shell member,
    csm_representative_incoming_edge_stack shell <>
      cmm_incoming_edge_stack member ->
    ck_incoming_edge_stack
      (observable (materialize_cohort_member shell member)) <>
    csm_representative_incoming_edge_stack shell.
Proof.
  intros shell member Hneq Heq.
  apply Hneq.
  symmetry.
  exact Heq.
Qed.

Record cohort_shell_evidence_model : Type := {
  csem_node : nat;
  csem_collection_depth : nat;
  csem_origin : option dispatch_key;
  csem_recovery_depth : nat;
  csem_sppf_baseline : option nat
}.

Lemma cohort_shell_evidence_eq_dec :
  forall x y : cohort_shell_evidence_model, {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply dispatch_key_eq_dec;
    try (decide equality; apply dispatch_key_eq_dec);
    try (decide equality; apply Nat.eq_dec).
Defined.

Record pending_member_model : Type := {
  pmm_shell_evidence : cohort_shell_evidence_model;
  pmm_incoming_edge_stack : nat;
  pmm_lex_stamp : option nat;
  pmm_weight : nat
}.

Inductive pending_member_storage : Type :=
  | CompactPendingMember
  | FullPendingMember.

Definition choose_pending_member_storage
    (shell : cohort_shell_evidence_model)
    (member : pending_member_model) : pending_member_storage :=
  if cohort_shell_evidence_eq_dec shell (pmm_shell_evidence member)
  then CompactPendingMember
  else FullPendingMember.

Definition materialize_stored_pending_member
    (shell : cohort_shell_evidence_model)
    (member : pending_member_model) : pending_member_model :=
  match choose_pending_member_storage shell member with
  | CompactPendingMember =>
      {| pmm_shell_evidence := shell;
         pmm_incoming_edge_stack := pmm_incoming_edge_stack member;
         pmm_lex_stamp := pmm_lex_stamp member;
         pmm_weight := pmm_weight member |}
  | FullPendingMember => member
  end.

Theorem compact_pending_member_requires_shell_evidence :
  forall shell member,
    choose_pending_member_storage shell member = CompactPendingMember ->
    shell = pmm_shell_evidence member.
Proof.
  intros shell member Hcompact.
  unfold choose_pending_member_storage in Hcompact.
  destruct (cohort_shell_evidence_eq_dec shell (pmm_shell_evidence member))
    as [Heq | Hneq].
  - exact Heq.
  - discriminate Hcompact.
Qed.

Theorem full_pending_member_preserves_incompatible_evidence :
  forall shell member,
    shell <> pmm_shell_evidence member ->
    materialize_stored_pending_member shell member = member.
Proof.
  intros shell member Hneq.
  unfold materialize_stored_pending_member, choose_pending_member_storage.
  destruct (cohort_shell_evidence_eq_dec shell (pmm_shell_evidence member))
    as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Theorem stored_pending_member_preserves_shell_evidence :
  forall shell member,
    pmm_shell_evidence (materialize_stored_pending_member shell member) =
      pmm_shell_evidence member.
Proof.
  intros shell member.
  unfold materialize_stored_pending_member, choose_pending_member_storage.
  destruct (cohort_shell_evidence_eq_dec shell (pmm_shell_evidence member))
    as [Heq | _].
  - exact Heq.
  - reflexivity.
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
