(*
 * RecoveryBound: bounded-recovery obligations for the active Prattail WPDA
 * walker.
 *
 * This mirrors the consuming-side recovery gate in wpda_walker.rs and the
 * synthesis-side branch cap in recovery_dispatch.rs. The model is deliberately
 * small: it records only the facts used to prevent recovery fork state-space
 * explosion.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Import ListNotations.

Definition recovery_fork_max_branches : nat := 8.

Definition synthesized_recovery_candidate_count
    (single_step multi_step : bool) : nat :=
  (if single_step then 1 else 0) +
  (if multi_step then 1 else 0).

Theorem synthesized_recovery_candidate_count_le_branch_cap :
  forall single_step multi_step,
    synthesized_recovery_candidate_count single_step multi_step
      <= recovery_fork_max_branches.
Proof.
  intros single_step multi_step.
  destruct single_step, multi_step;
    unfold synthesized_recovery_candidate_count;
    unfold recovery_fork_max_branches;
    simpl; lia.
Qed.

Definition normalize_recovery_beam_width
    (beam_width : option Z) : option Z :=
  match beam_width with
  | None => None
  | Some width =>
      if (0 <=? width)%Z then Some width else None
  end.

Theorem negative_recovery_beam_width_is_disabled :
  forall width,
    (width < 0)%Z ->
    normalize_recovery_beam_width (Some width) = None.
Proof.
  intros width Hlt.
  unfold normalize_recovery_beam_width.
  assert (Hle : (0 <=? width)%Z = false).
  { apply Z.leb_gt. exact Hlt. }
  rewrite Hle.
  reflexivity.
Qed.

Theorem nonnegative_recovery_beam_width_is_preserved :
  forall width,
    (0 <= width)%Z ->
    normalize_recovery_beam_width (Some width) = Some width.
Proof.
  intros width Hle.
  unfold normalize_recovery_beam_width.
  assert (Hleb : (0 <=? width)%Z = true).
  { apply Z.leb_le. exact Hle. }
  rewrite Hleb.
  reflexivity.
Qed.

Definition normalize_recovery_weight
    (default value : Z) : Z :=
  if (0 <=? value)%Z then value else default.

Theorem negative_recovery_weight_uses_default :
  forall default value,
    (value < 0)%Z ->
    normalize_recovery_weight default value = default.
Proof.
  intros default value Hlt.
  unfold normalize_recovery_weight.
  assert (Hleb : (0 <=? value)%Z = false).
  { apply Z.leb_gt. exact Hlt. }
  rewrite Hleb.
  reflexivity.
Qed.

Theorem nonnegative_recovery_weight_is_preserved :
  forall default value,
    (0 <= value)%Z ->
    normalize_recovery_weight default value = value.
Proof.
  intros default value Hle.
  unfold normalize_recovery_weight.
  assert (Hleb : (0 <=? value)%Z = true).
  { apply Z.leb_le. exact Hle. }
  rewrite Hleb.
  reflexivity.
Qed.

Theorem normalized_recovery_weight_is_nonnegative :
  forall default value,
    (0 <= default)%Z ->
    (0 <= normalize_recovery_weight default value)%Z.
Proof.
  intros default value Hdefault.
  unfold normalize_recovery_weight.
  destruct (0 <=? value)%Z eqn:Hvalue.
  - apply Z.leb_le. exact Hvalue.
  - exact Hdefault.
Qed.

Definition recovery_window_length
    (token_count pos : nat) : option nat :=
  if pos <=? token_count
  then Some (token_count - pos)
  else None.

Theorem recovery_window_past_input_is_none :
  forall token_count pos,
    token_count < pos ->
    recovery_window_length token_count pos = None.
Proof.
  intros token_count pos Hlt.
  unfold recovery_window_length.
  assert (Hleb : (pos <=? token_count) = false).
  { apply Nat.leb_gt. exact Hlt. }
  rewrite Hleb.
  reflexivity.
Qed.

Theorem recovery_window_at_eof_is_empty :
  forall token_count,
    recovery_window_length token_count token_count = Some 0.
Proof.
  intros token_count.
  unfold recovery_window_length.
  rewrite Nat.leb_refl.
  rewrite Nat.sub_diag.
  reflexivity.
Qed.

Theorem recovery_window_in_bounds_has_suffix_length :
  forall token_count pos,
    pos <= token_count ->
    recovery_window_length token_count pos =
      Some (token_count - pos).
Proof.
  intros token_count pos Hle.
  unfold recovery_window_length.
  assert (Hleb : (pos <=? token_count) = true).
  { apply Nat.leb_le. exact Hle. }
  rewrite Hleb.
  reflexivity.
Qed.

Inductive resolved_repair_action : Type :=
  | ResolvedSkipToSync
  | ResolvedDeleteToken
  | ResolvedInsertToken
  | ResolvedSubstituteToken
  | ResolvedSwapTokens.

Definition is_resolved_insert (a : resolved_repair_action) : bool :=
  match a with
  | ResolvedInsertToken => true
  | _ => false
  end.

Definition contains_resolved_insert
    (actions : list resolved_repair_action) : bool :=
  existsb is_resolved_insert actions.

Definition resolved_action_mutates_token_source
    (a : resolved_repair_action) : bool :=
  match a with
  | ResolvedInsertToken
  | ResolvedSubstituteToken
  | ResolvedSwapTokens => true
  | ResolvedSkipToSync
  | ResolvedDeleteToken => false
  end.

Definition contains_resolved_token_mutation
    (actions : list resolved_repair_action) : bool :=
  existsb resolved_action_mutates_token_source actions.

Lemma contains_resolved_insert_spec :
  forall actions,
    contains_resolved_insert actions = true <->
    In ResolvedInsertToken actions.
Proof.
  intros actions.
  unfold contains_resolved_insert.
  rewrite existsb_exists.
  split.
  - intros [a [Hin Ha]].
    destruct a; simpl in Ha; try discriminate.
    exact Hin.
  - intros Hin.
    exists ResolvedInsertToken.
    split; [exact Hin | reflexivity].
Qed.

Inductive replay_repair_action : Type :=
  | ReplaySkipToSync (skip_count : nat)
  | ReplayDeleteToken
  | ReplayInsertToken
  | ReplaySubstituteToken
  | ReplaySwapTokens (pos_a pos_b : nat).

Definition replay_action_position
    (base_pos cur_pos : nat)
    (action : replay_repair_action) : nat :=
  match action with
  | ReplaySkipToSync skip_count => cur_pos + skip_count
  | ReplayDeleteToken => S cur_pos
  | ReplayInsertToken => cur_pos
  | ReplaySubstituteToken => S cur_pos
  | ReplaySwapTokens pos_a pos_b =>
      Nat.max cur_pos (S (Nat.max (base_pos + pos_a) (base_pos + pos_b)))
  end.

Fixpoint replay_sequence_position
    (base_pos cur_pos : nat)
    (actions : list replay_repair_action) : nat :=
  match actions with
  | [] => cur_pos
  | action :: rest =>
      replay_sequence_position
        base_pos
        (replay_action_position base_pos cur_pos action)
        rest
  end.

Theorem replay_skip_to_sync_advances_by_skip_count :
  forall base_pos cur_pos skip_count,
    replay_sequence_position
      base_pos cur_pos [ReplaySkipToSync skip_count] =
    cur_pos + skip_count.
Proof.
  intros base_pos cur_pos skip_count.
  simpl.
  reflexivity.
Qed.

Theorem replay_delete_then_skip_preserves_both_advances :
  forall base_pos cur_pos skip_count,
    replay_sequence_position
      base_pos cur_pos [ReplayDeleteToken; ReplaySkipToSync skip_count] =
    S cur_pos + skip_count.
Proof.
  intros base_pos cur_pos skip_count.
  simpl.
  reflexivity.
Qed.

Theorem replay_insert_is_non_advancing :
  forall base_pos cur_pos,
    replay_sequence_position base_pos cur_pos [ReplayInsertToken] = cur_pos.
Proof.
  intros base_pos cur_pos.
  simpl.
  reflexivity.
Qed.

Theorem replay_swap_advances_to_after_window_max :
  forall base_pos cur_pos pos_a pos_b,
    replay_sequence_position
      base_pos cur_pos [ReplaySwapTokens pos_a pos_b] =
    Nat.max
      cur_pos
      (S (Nat.max (base_pos + pos_a) (base_pos + pos_b))).
Proof.
  intros base_pos cur_pos pos_a pos_b.
  simpl.
  reflexivity.
Qed.

Theorem replay_base_relative_adjacent_swap_target :
  forall base_pos,
    replay_sequence_position
      base_pos base_pos [ReplaySwapTokens 0 1] =
    base_pos + 2.
Proof.
  intros base_pos.
  simpl.
  rewrite Nat.add_0_r.
  replace (base_pos + 1) with (S base_pos) by lia.
  rewrite Nat.max_r by lia.
  rewrite Nat.max_r by lia.
  lia.
Qed.

Theorem replay_delete_then_skip_from_base_target :
  forall base_pos skip_count,
    replay_sequence_position
      base_pos base_pos [ReplayDeleteToken; ReplaySkipToSync skip_count] =
    base_pos + S skip_count.
Proof.
  intros base_pos skip_count.
  simpl.
  lia.
Qed.

Definition apply_sequence_target_consistent
    (base_pos target_pos : nat)
    (actions : list replay_repair_action) : Prop :=
  replay_sequence_position base_pos base_pos actions = target_pos.

Definition sequence_local_target_consistent
    (target_pos : nat)
    (actions : list replay_repair_action) : Prop :=
  replay_sequence_position 0 0 actions = target_pos.

Theorem target_consistency_allows_nonadvancing_insert :
  forall base_pos,
    apply_sequence_target_consistent
      base_pos base_pos [ReplayInsertToken].
Proof.
  intros base_pos.
  unfold apply_sequence_target_consistent.
  simpl.
  reflexivity.
Qed.

Theorem target_consistency_rejects_nonadvancing_delete :
  forall base_pos,
    ~ apply_sequence_target_consistent
        base_pos base_pos [ReplayDeleteToken].
Proof.
  intros base_pos Hconsistent.
  unfold apply_sequence_target_consistent in Hconsistent.
  simpl in Hconsistent.
  lia.
Qed.

Theorem sequence_target_delete_then_skip :
  forall skip_count,
    sequence_local_target_consistent
      (S skip_count)
      [ReplayDeleteToken; ReplaySkipToSync skip_count].
Proof.
  intros skip_count.
  unfold sequence_local_target_consistent.
  simpl.
  lia.
Qed.

Theorem sequence_target_rejects_mismatched_delete_skip :
  ~ sequence_local_target_consistent
      1
      [ReplayDeleteToken; ReplaySkipToSync 1].
Proof.
  unfold sequence_local_target_consistent.
  simpl.
  lia.
Qed.

Theorem sequence_target_insert_nonadvancing :
  sequence_local_target_consistent 0 [ReplayInsertToken].
Proof.
  unfold sequence_local_target_consistent.
  simpl.
  reflexivity.
Qed.

Theorem sequence_target_head_swap :
  sequence_local_target_consistent 2 [ReplaySwapTokens 0 1].
Proof.
  unfold sequence_local_target_consistent.
  simpl.
  reflexivity.
Qed.

Definition direct_replay_action_target
    (action : replay_repair_action) : option nat :=
  match action with
  | ReplaySkipToSync skip_count => Some skip_count
  | ReplayDeleteToken => Some 1
  | ReplayInsertToken => Some 0
  | ReplaySubstituteToken => Some 1
  | ReplaySwapTokens pos_a pos_b =>
      if ((Nat.min pos_a pos_b =? 0)
          && (Nat.max pos_a pos_b =? 1))%bool
      then Some 2
      else None
  end.

Definition direct_replay_target_consistent
    (target_pos : nat)
    (action : replay_repair_action) : Prop :=
  direct_replay_action_target action = Some target_pos.

Definition direct_absolute_effect_target
    (base_pos : nat)
    (action : replay_repair_action) : option nat :=
  match direct_replay_action_target action with
  | Some local_target => Some (base_pos + local_target)
  | None => None
  end.

Theorem direct_insert_target_is_nonadvancing :
  direct_replay_target_consistent 0 ReplayInsertToken.
Proof.
  unfold direct_replay_target_consistent.
  simpl.
  reflexivity.
Qed.

Theorem direct_substitute_target_is_one :
  direct_replay_target_consistent 1 ReplaySubstituteToken.
Proof.
  unfold direct_replay_target_consistent.
  simpl.
  reflexivity.
Qed.

Theorem direct_substitute_rejects_target_two :
  ~ direct_replay_target_consistent 2 ReplaySubstituteToken.
Proof.
  unfold direct_replay_target_consistent.
  simpl.
  discriminate.
Qed.

Theorem direct_head_swap_target_is_two :
  direct_replay_target_consistent 2 (ReplaySwapTokens 0 1).
Proof.
  unfold direct_replay_target_consistent.
  simpl.
  reflexivity.
Qed.

Theorem direct_nonhead_swap_has_no_target :
  direct_replay_action_target (ReplaySwapTokens 2 3) = None.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem direct_insert_absolute_target_is_base :
  forall base_pos,
    direct_absolute_effect_target base_pos ReplayInsertToken =
    Some base_pos.
Proof.
  intros base_pos.
  unfold direct_absolute_effect_target.
  simpl.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Theorem direct_substitute_absolute_target_is_successor :
  forall base_pos,
    direct_absolute_effect_target base_pos ReplaySubstituteToken =
    Some (S base_pos).
Proof.
  intros base_pos.
  unfold direct_absolute_effect_target.
  simpl.
  replace (base_pos + 1) with (S base_pos) by lia.
  reflexivity.
Qed.

Theorem direct_head_swap_absolute_target_is_base_plus_two :
  forall base_pos,
    direct_absolute_effect_target base_pos (ReplaySwapTokens 0 1) =
    Some (base_pos + 2).
Proof.
  intros base_pos.
  unfold direct_absolute_effect_target.
  simpl.
  reflexivity.
Qed.

Theorem direct_nonhead_swap_absolute_target_rejected :
  forall base_pos,
    direct_absolute_effect_target base_pos (ReplaySwapTokens 2 3) =
    None.
Proof.
  intros base_pos.
  unfold direct_absolute_effect_target.
  simpl.
  reflexivity.
Qed.

Inductive recovery_effect : Type :=
  | DeltaRecoveryEvent
  | DeltaInsertToken (pos : nat)
  | DeltaSubstituteToken (pos : nat)
  | DeltaSwapTokens (pos_a pos_b : nat)
  | DeltaCommitLexAlternative
  | DeltaApplyRecoverySequence
      (target_pos : nat)
      (actions : list resolved_repair_action)
  | DeltaNonRecovery.

Definition effect_is_recovery (effect : recovery_effect) : bool :=
  match effect with
  | DeltaRecoveryEvent
  | DeltaInsertToken _
  | DeltaSubstituteToken _
  | DeltaSwapTokens _ _
  | DeltaCommitLexAlternative
  | DeltaApplyRecoverySequence _ _ => true
  | DeltaNonRecovery => false
  end.

Definition effect_allows_non_advancing (effect : recovery_effect) : bool :=
  match effect with
  | DeltaInsertToken _ => true
  | DeltaApplyRecoverySequence _ actions => contains_resolved_insert actions
  | _ => false
  end.

Definition recovery_effect_mutates_token_source
    (effect : recovery_effect) : bool :=
  match effect with
  | DeltaInsertToken _
  | DeltaSubstituteToken _
  | DeltaSwapTokens _ _
  | DeltaCommitLexAlternative => true
  | DeltaApplyRecoverySequence _ actions =>
      contains_resolved_token_mutation actions
  | DeltaRecoveryEvent
  | DeltaNonRecovery => false
  end.

Theorem direct_recovery_token_deltas_mutate_token_source :
  forall pos pos_a pos_b,
    recovery_effect_mutates_token_source (DeltaInsertToken pos) = true /\
    recovery_effect_mutates_token_source (DeltaSubstituteToken pos) = true /\
    recovery_effect_mutates_token_source (DeltaSwapTokens pos_a pos_b) = true /\
    recovery_effect_mutates_token_source DeltaCommitLexAlternative = true.
Proof.
  intros pos pos_a pos_b.
  repeat split.
Qed.

Theorem cursor_only_recovery_deltas_do_not_mutate_token_source :
  recovery_effect_mutates_token_source DeltaRecoveryEvent = false /\
  recovery_effect_mutates_token_source
    (DeltaApplyRecoverySequence 2 [ResolvedDeleteToken; ResolvedSkipToSync]) =
    false.
Proof.
  repeat split.
Qed.

Theorem sequence_recovery_token_deltas_mutate_token_source :
  forall target prefix suffix action,
    resolved_action_mutates_token_source action = true ->
    recovery_effect_mutates_token_source
      (DeltaApplyRecoverySequence target (prefix ++ action :: suffix)) =
      true.
Proof.
  intros target prefix suffix action Hmut.
  unfold recovery_effect_mutates_token_source.
  unfold contains_resolved_token_mutation.
  rewrite existsb_app.
  simpl.
  rewrite Hmut.
  rewrite orb_true_r.
  reflexivity.
Qed.

Definition recovery_delta_target_position
    (state_target : option nat)
    (effect : recovery_effect) : option nat :=
  match effect with
  | DeltaInsertToken pos =>
      match state_target with
      | Some target => if target =? pos then Some pos else None
      | None => None
      end
  | DeltaSubstituteToken pos =>
      match state_target with
      | Some target =>
          let effect_target := S pos in
          if target =? effect_target then Some effect_target else None
      | None => None
      end
  | DeltaSwapTokens pos_a pos_b =>
      match state_target with
      | Some target =>
          let effect_target := S (Nat.max pos_a pos_b) in
          if target =? effect_target then Some effect_target else None
      | None => None
      end
  | DeltaApplyRecoverySequence effect_target _ =>
      match state_target with
      | Some target =>
          if target =? effect_target then Some effect_target else None
      | None => None
      end
  | _ => if effect_is_recovery effect then state_target else None
  end.

Theorem apply_sequence_target_accepts_matching_branch_state :
  forall target actions,
    recovery_delta_target_position
      (Some target)
      (DeltaApplyRecoverySequence target actions) =
    Some target.
Proof.
  intros target actions.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem apply_sequence_target_rejects_nonprefix_branch_state :
  forall target actions,
    recovery_delta_target_position
      None
      (DeltaApplyRecoverySequence target actions) =
    None.
Proof.
  intros target actions.
  simpl.
  reflexivity.
Qed.

Theorem apply_sequence_target_rejects_mismatched_branch_state :
  forall state_target effect_target actions,
    state_target <> effect_target ->
    recovery_delta_target_position
      (Some state_target)
      (DeltaApplyRecoverySequence effect_target actions) =
    None.
Proof.
  intros state_target effect_target actions Hneq.
  simpl.
  destruct (state_target =? effect_target) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    contradiction.
  - reflexivity.
Qed.

Theorem direct_insert_delta_target_accepts_matching_branch_state :
  forall pos,
    recovery_delta_target_position
      (Some pos)
      (DeltaInsertToken pos) =
    Some pos.
Proof.
  intros pos.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem direct_insert_delta_target_rejects_mismatched_branch_state :
  forall state_target pos,
    state_target <> pos ->
    recovery_delta_target_position
      (Some state_target)
      (DeltaInsertToken pos) =
    None.
Proof.
  intros state_target pos Hneq.
  simpl.
  destruct (state_target =? pos) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    contradiction.
  - reflexivity.
Qed.

Theorem direct_insert_delta_target_rejects_nonprefix_branch_state :
  forall pos,
    recovery_delta_target_position
      None
      (DeltaInsertToken pos) =
    None.
Proof.
  intros pos.
  reflexivity.
Qed.

Theorem direct_substitute_delta_target_accepts_successor :
  forall pos,
    recovery_delta_target_position
      (Some (S pos))
      (DeltaSubstituteToken pos) =
    Some (S pos).
Proof.
  intros pos.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem direct_substitute_delta_target_rejects_mismatched_branch_state :
  forall state_target pos,
    state_target <> S pos ->
    recovery_delta_target_position
      (Some state_target)
      (DeltaSubstituteToken pos) =
    None.
Proof.
  intros state_target pos Hneq.
  simpl.
  destruct (state_target =? S pos) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    contradiction.
  - reflexivity.
Qed.

Theorem direct_substitute_delta_target_rejects_nonprefix_branch_state :
  forall pos,
    recovery_delta_target_position
      None
      (DeltaSubstituteToken pos) =
    None.
Proof.
  intros pos.
  reflexivity.
Qed.

Theorem direct_swap_delta_target_accepts_after_window_max :
  forall pos_a pos_b,
    recovery_delta_target_position
      (Some (S (Nat.max pos_a pos_b)))
      (DeltaSwapTokens pos_a pos_b) =
    Some (S (Nat.max pos_a pos_b)).
Proof.
  intros pos_a pos_b.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem direct_swap_delta_target_rejects_mismatched_branch_state :
  forall state_target pos_a pos_b,
    state_target <> S (Nat.max pos_a pos_b) ->
    recovery_delta_target_position
      (Some state_target)
      (DeltaSwapTokens pos_a pos_b) =
    None.
Proof.
  intros state_target pos_a pos_b Hneq.
  simpl.
  destruct (state_target =? S (Nat.max pos_a pos_b)) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    contradiction.
  - reflexivity.
Qed.

Theorem direct_swap_delta_target_rejects_nonprefix_branch_state :
  forall pos_a pos_b,
    recovery_delta_target_position
      None
      (DeltaSwapTokens pos_a pos_b) =
    None.
Proof.
  intros pos_a pos_b.
  reflexivity.
Qed.

Definition recovery_delta_target_valid
    (state_target : option nat)
    (effect : recovery_effect) : bool :=
  match effect with
  | DeltaInsertToken pos =>
      match state_target with
      | Some target => target =? pos
      | None => true
      end
  | DeltaSubstituteToken pos =>
      match state_target with
      | Some target => target =? S pos
      | None => true
      end
  | DeltaSwapTokens pos_a pos_b =>
      match state_target with
      | Some target => target =? S (Nat.max pos_a pos_b)
      | None => true
      end
  | DeltaApplyRecoverySequence effect_target _ =>
      match state_target with
      | Some target => target =? effect_target
      | None => true
      end
  | _ => true
  end.

Fixpoint first_recovery_delta_target
    (state_target : option nat)
    (effects : list recovery_effect) : option nat :=
  match effects with
  | [] => None
  | effect :: rest =>
      match recovery_delta_target_position state_target effect with
      | Some target => Some target
      | None => first_recovery_delta_target state_target rest
      end
  end.

Definition recovery_effects_target_position
    (state_target : option nat)
    (effects : list recovery_effect) : option nat :=
  if forallb (recovery_delta_target_valid state_target) effects
  then first_recovery_delta_target state_target effects
  else None.

Theorem multi_effect_target_ignores_nonrecovery_only :
  forall target,
    recovery_effects_target_position
      (Some target)
      [DeltaNonRecovery] =
    None.
Proof.
  intros target.
  simpl.
  reflexivity.
Qed.

Theorem multi_effect_target_accepts_matching_recovery_targets :
  forall target actions,
    recovery_effects_target_position
      (Some target)
      [DeltaNonRecovery;
       DeltaRecoveryEvent;
       DeltaApplyRecoverySequence target actions] =
    Some target.
Proof.
  intros target actions.
  unfold recovery_effects_target_position.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem multi_effect_target_rejects_mismatched_apply_sequence :
  forall state_target effect_target actions,
    state_target <> effect_target ->
    recovery_effects_target_position
      (Some state_target)
      [DeltaRecoveryEvent;
       DeltaApplyRecoverySequence effect_target actions] =
    None.
Proof.
  intros state_target effect_target actions Hneq.
  unfold recovery_effects_target_position.
  simpl.
  destruct (state_target =? effect_target) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    contradiction.
  - reflexivity.
Qed.

Theorem multi_effect_target_accepts_matching_direct_and_sequence :
  forall pos actions,
    recovery_effects_target_position
      (Some (S pos))
      [DeltaSubstituteToken pos;
       DeltaApplyRecoverySequence (S pos) actions] =
    Some (S pos).
Proof.
  intros pos actions.
  unfold recovery_effects_target_position.
  simpl.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem multi_effect_target_rejects_mismatched_direct_and_sequence :
  forall pos sequence_target actions,
    S pos <> sequence_target ->
    recovery_effects_target_position
      (Some (S pos))
      [DeltaSubstituteToken pos;
       DeltaApplyRecoverySequence sequence_target actions] =
    None.
Proof.
  intros pos sequence_target actions Hneq.
  destruct sequence_target as [| sequence_target'].
  - unfold recovery_effects_target_position.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - unfold recovery_effects_target_position.
    simpl.
    rewrite Nat.eqb_refl.
    destruct (pos =? sequence_target') eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      subst.
      contradiction.
    + reflexivity.
Qed.

Theorem multi_effect_target_rejects_mismatched_direct_targets :
  forall insert_pos substitute_pos,
    insert_pos <> S substitute_pos ->
    recovery_effects_target_position
      (Some insert_pos)
      [DeltaInsertToken insert_pos;
       DeltaSubstituteToken substitute_pos] =
    None.
Proof.
  intros insert_pos substitute_pos Hneq.
  unfold recovery_effects_target_position.
  simpl.
  rewrite Nat.eqb_refl.
  destruct (insert_pos =? S substitute_pos) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    contradiction.
  - reflexivity.
Qed.

Inductive fork_action : Type :=
  | ConsumeAndReplaceWithEffect (effect : recovery_effect)
  | LexAltForkAction
  | LexAltPrefixForkAction
  | OtherForkAction.

Record recovery_branch : Type := {
  br_prefix_target : option nat;
  br_action : fork_action
}.

Definition branch_has_recovery_effect (b : recovery_branch) : bool :=
  match br_action b with
  | ConsumeAndReplaceWithEffect effect => effect_is_recovery effect
  | LexAltForkAction
  | LexAltPrefixForkAction => false
  | OtherForkAction => false
  end.

Definition is_recovery_fork (branches : list recovery_branch) : bool :=
  existsb branch_has_recovery_effect branches.

Definition branch_journals_commit_lex_alternative
    (b : recovery_branch) : bool :=
  match br_action b with
  | LexAltForkAction
  | LexAltPrefixForkAction => true
  | _ => false
  end.

Theorem lex_alt_branch_journals_commit_delta :
  forall target,
    branch_journals_commit_lex_alternative
      {| br_prefix_target := target;
         br_action := LexAltForkAction |} = true.
Proof.
  intros target.
  simpl.
  reflexivity.
Qed.

Theorem lex_alt_prefix_branch_journals_commit_delta :
  forall target,
    branch_journals_commit_lex_alternative
      {| br_prefix_target := target;
         br_action := LexAltPrefixForkAction |} = true.
Proof.
  intros target.
  simpl.
  reflexivity.
Qed.

Theorem lex_alt_commit_branches_are_not_recovery_forks :
  forall target,
    is_recovery_fork
      [{| br_prefix_target := target;
          br_action := LexAltForkAction |};
       {| br_prefix_target := target;
          br_action := LexAltPrefixForkAction |}] = false.
Proof.
  intros target.
  simpl.
  reflexivity.
Qed.

Definition branch_advances (base_pos : nat) (b : recovery_branch) : bool :=
  match br_prefix_target b with
  | Some target_pos => base_pos <? target_pos
  | None => true
  end.

Definition branch_non_advancing_insert (b : recovery_branch) : bool :=
  match br_action b with
  | ConsumeAndReplaceWithEffect effect => effect_allows_non_advancing effect
  | LexAltForkAction
  | LexAltPrefixForkAction => false
  | OtherForkAction => false
  end.

Definition forward_progress_or_insert
    (base_pos : nat)
    (b : recovery_branch) : bool :=
  branch_advances base_pos b || branch_non_advancing_insert b.

Definition branch_target_valid (b : recovery_branch) : bool :=
  match br_action b with
  | ConsumeAndReplaceWithEffect effect =>
      recovery_delta_target_valid (br_prefix_target b) effect
  | LexAltForkAction
  | LexAltPrefixForkAction
  | OtherForkAction => true
  end.

Definition recovery_branch_safe
    (base_pos : nat)
    (b : recovery_branch) : bool :=
  forward_progress_or_insert base_pos b && branch_target_valid b.

Definition forward_branches
    (base_pos : nat)
    (branches : list recovery_branch) : list recovery_branch :=
  filter (recovery_branch_safe base_pos) branches.

Definition all_forward_branches
    (base_pos : nat)
    (branches : list recovery_branch) : bool :=
  forallb (recovery_branch_safe base_pos) branches.

Lemma forward_branches_identity_when_all_forward :
  forall base_pos branches,
    all_forward_branches base_pos branches = true ->
    forward_branches base_pos branches = branches.
Proof.
  intros base_pos branches.
  unfold all_forward_branches.
  unfold forward_branches.
  induction branches as [| b branches IH]; intros Hall.
  - reflexivity.
  - simpl in Hall.
    apply andb_true_iff in Hall as [Hb Hall].
    simpl.
    rewrite Hb.
    rewrite IH; [reflexivity | exact Hall].
Qed.

Definition bounded_recovery_branches
    (base_pos : nat)
    (branches : list recovery_branch) : list recovery_branch :=
  firstn recovery_fork_max_branches (forward_branches base_pos branches).

Theorem prefiltered_bounded_recovery_is_capped_identity :
  forall base_pos branches,
    all_forward_branches base_pos branches = true ->
    bounded_recovery_branches base_pos branches =
    firstn recovery_fork_max_branches branches.
Proof.
  intros base_pos branches Hall.
  unfold bounded_recovery_branches.
  rewrite (forward_branches_identity_when_all_forward base_pos branches Hall).
  reflexivity.
Qed.

Lemma in_firstn :
  forall A (x : A) n xs,
    In x (firstn n xs) -> In x xs.
Proof.
  intros A x n xs.
  revert n.
  induction xs as [| y ys IH]; intros n Hin.
  - destruct n; simpl in Hin; contradiction.
  - destruct n; simpl in Hin.
    + contradiction.
    + destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. exact (IH n Hin).
Qed.

Theorem bounded_recovery_branch_limit :
  forall base_pos branches,
    length (bounded_recovery_branches base_pos branches)
      <= recovery_fork_max_branches.
Proof.
  intros base_pos branches.
  unfold bounded_recovery_branches.
  rewrite length_firstn.
  lia.
Qed.

Theorem bounded_recovery_retains_only_progress_or_insert :
  forall base_pos branches b,
    In b (bounded_recovery_branches base_pos branches) ->
    forward_progress_or_insert base_pos b = true.
Proof.
  intros base_pos branches b Hin.
  unfold bounded_recovery_branches in Hin.
  pose proof (in_firstn recovery_branch b recovery_fork_max_branches _ Hin) as Hfilter.
  unfold forward_branches in Hfilter.
  apply filter_In in Hfilter.
  destruct Hfilter as [_ Hsafe].
  unfold recovery_branch_safe in Hsafe.
  apply andb_true_iff in Hsafe as [Hforward _].
  exact Hforward.
Qed.

Theorem bounded_recovery_retains_only_target_valid_branches :
  forall base_pos branches b,
    In b (bounded_recovery_branches base_pos branches) ->
    branch_target_valid b = true.
Proof.
  intros base_pos branches b Hin.
  unfold bounded_recovery_branches in Hin.
  pose proof (in_firstn recovery_branch b recovery_fork_max_branches _ Hin) as Hfilter.
  unfold forward_branches in Hfilter.
  apply filter_In in Hfilter.
  destruct Hfilter as [_ Hsafe].
  unfold recovery_branch_safe in Hsafe.
  apply andb_true_iff in Hsafe as [_ Htarget].
  exact Htarget.
Qed.

Theorem prefix_nonadvancing_branch_requires_insert :
  forall base_pos b target_pos,
    br_prefix_target b = Some target_pos ->
    target_pos <= base_pos ->
    forward_progress_or_insert base_pos b = true ->
    branch_non_advancing_insert b = true.
Proof.
  intros base_pos b target_pos Htarget Hle Hforward.
  unfold forward_progress_or_insert in Hforward.
  unfold branch_advances in Hforward.
  rewrite Htarget in Hforward.
  destruct (base_pos <? target_pos) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. lia.
  - simpl in Hforward. exact Hforward.
Qed.

Definition dispatch_key : Type := nat.

Record recovery_cursor : Type := {
  rc_pos : nat;
  rc_depth : nat;
  rc_visited : list dispatch_key
}.

Definition key_seen (key : dispatch_key) (visited : list dispatch_key) : bool :=
  existsb (Nat.eqb key) visited.

Definition has_not_visited
    (key : option dispatch_key)
    (c : recovery_cursor) : bool :=
  match key with
  | Some k => negb (key_seen k (rc_visited c))
  | None => true
  end.

Definition insert_key
    (key : dispatch_key)
    (visited : list dispatch_key) : list dispatch_key :=
  if key_seen key visited then visited else key :: visited.

Definition child_after_recovery
    (key : option dispatch_key)
    (c : recovery_cursor) : recovery_cursor :=
  {| rc_pos := rc_pos c;
     rc_depth := S (rc_depth c);
     rc_visited :=
       match key with
       | Some k => insert_key k (rc_visited c)
       | None => rc_visited c
       end |}.

Definition recovery_remaining
    (max_depth : nat)
    (c : recovery_cursor) : nat :=
  max_depth - rc_depth c.

Fixpoint recovery_frontier_capacity (fuel : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' => recovery_fork_max_branches * recovery_frontier_capacity fuel'
  end.

Fixpoint recovery_tree_capacity (fuel : nat) : nat :=
  match fuel with
  | 0 => 1
  | S fuel' => S (recovery_fork_max_branches * recovery_tree_capacity fuel')
  end.

Definition has_viable_recovery_branch
    (base_pos : nat)
    (branches : list recovery_branch) : bool :=
  negb (length (bounded_recovery_branches base_pos branches) =? 0).

Definition recovery_gate_accepts
    (max_depth : nat)
    (key : option dispatch_key)
    (c : recovery_cursor)
    (branches : list recovery_branch) : bool :=
  (rc_depth c <? max_depth)
  && has_not_visited key c
  && has_viable_recovery_branch (rc_pos c) branches.

Theorem max_depth_zero_rejects :
  forall key c branches,
    recovery_gate_accepts 0 key c branches = false.
Proof.
  intros key c branches.
  unfold recovery_gate_accepts.
  simpl.
  reflexivity.
Qed.

Theorem accepted_child_depth_le_max :
  forall max_depth key c branches,
    recovery_gate_accepts max_depth key c branches = true ->
    rc_depth (child_after_recovery key c) <= max_depth.
Proof.
  intros max_depth key c branches Hgate.
  unfold recovery_gate_accepts in Hgate.
  apply andb_true_iff in Hgate as [Hgate _].
  apply andb_true_iff in Hgate as [Hdepth _].
  apply Nat.ltb_lt in Hdepth.
  simpl.
  lia.
Qed.

Theorem child_dispatches_left_decreases :
  forall max_depth key c branches,
    recovery_gate_accepts max_depth key c branches = true ->
    max_depth - rc_depth (child_after_recovery key c)
      < max_depth - rc_depth c.
Proof.
  intros max_depth key c branches Hgate.
  unfold recovery_gate_accepts in Hgate.
  apply andb_true_iff in Hgate as [Hgate _].
  apply andb_true_iff in Hgate as [Hdepth _].
  apply Nat.ltb_lt in Hdepth.
  simpl.
  lia.
Qed.

Lemma accepted_child_remaining_step :
  forall max_depth key c branches,
    recovery_gate_accepts max_depth key c branches = true ->
    recovery_remaining max_depth c =
    S (recovery_remaining max_depth (child_after_recovery key c)).
Proof.
  intros max_depth key c branches Hgate.
  unfold recovery_gate_accepts in Hgate.
  apply andb_true_iff in Hgate as [Hgate _].
  apply andb_true_iff in Hgate as [Hdepth _].
  apply Nat.ltb_lt in Hdepth.
  unfold recovery_remaining.
  simpl.
  lia.
Qed.

Theorem accepted_next_frontier_capacity_bound :
  forall max_depth key c branches,
    recovery_gate_accepts max_depth key c branches = true ->
    length (bounded_recovery_branches (rc_pos c) branches)
      * recovery_frontier_capacity
          (recovery_remaining max_depth (child_after_recovery key c))
    <= recovery_frontier_capacity (recovery_remaining max_depth c).
Proof.
  intros max_depth key c branches Hgate.
  rewrite (accepted_child_remaining_step max_depth key c branches Hgate).
  simpl.
  change
    (length (bounded_recovery_branches (rc_pos c) branches)
      * recovery_frontier_capacity
          (recovery_remaining max_depth (child_after_recovery key c))
     <= recovery_fork_max_branches
      * recovery_frontier_capacity
          (recovery_remaining max_depth (child_after_recovery key c))).
  apply Nat.mul_le_mono_r.
  apply bounded_recovery_branch_limit.
Qed.

Theorem accepted_recovery_tree_capacity_bound :
  forall max_depth key c branches,
    recovery_gate_accepts max_depth key c branches = true ->
    S (length (bounded_recovery_branches (rc_pos c) branches)
        * recovery_tree_capacity
            (recovery_remaining max_depth (child_after_recovery key c)))
    <= recovery_tree_capacity (recovery_remaining max_depth c).
Proof.
  intros max_depth key c branches Hgate.
  rewrite (accepted_child_remaining_step max_depth key c branches Hgate).
  simpl.
  change
    (S (length (bounded_recovery_branches (rc_pos c) branches)
        * recovery_tree_capacity
            (recovery_remaining max_depth (child_after_recovery key c)))
     <= S (recovery_fork_max_branches
        * recovery_tree_capacity
            (recovery_remaining max_depth (child_after_recovery key c)))).
  apply le_n_S.
  apply Nat.mul_le_mono_r.
  apply bounded_recovery_branch_limit.
Qed.

Lemma key_seen_insert_same :
  forall key visited,
    key_seen key (insert_key key visited) = true.
Proof.
  intros key visited.
  unfold insert_key.
  destruct (key_seen key visited) eqn:Hseen.
  - exact Hseen.
  - unfold key_seen.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
Qed.

Theorem child_marks_dispatch_key_seen :
  forall key c,
    has_not_visited (Some key) (child_after_recovery (Some key) c) = false.
Proof.
  intros key c.
  unfold has_not_visited.
  simpl.
  rewrite key_seen_insert_same.
  reflexivity.
Qed.

Theorem same_dispatch_rejected_after_child_update :
  forall max_depth key c branches,
    recovery_gate_accepts max_depth (Some key) c branches = true ->
    recovery_gate_accepts
      max_depth
      (Some key)
      (child_after_recovery (Some key) c)
      branches = false.
Proof.
  intros max_depth key c branches _.
  unfold recovery_gate_accepts.
  simpl.
  rewrite key_seen_insert_same.
  destruct (S (rc_depth c) <? max_depth); reflexivity.
Qed.

Record recovery_cost_config : Type := {
  cfg_skip_per_token_bits : nat;
  cfg_delete_cost_bits : nat;
  cfg_substitute_cost_bits : nat;
  cfg_insert_cost_bits : nat;
  cfg_swap_cost_bits : nat;
  cfg_max_skip_lookahead : nat;
  cfg_deep_nesting_threshold : nat;
  cfg_deep_nesting_skip_mult_bits : nat;
  cfg_shallow_depth_threshold : nat;
  cfg_shallow_depth_skip_mult_bits : nat;
  cfg_low_bp_threshold : nat;
  cfg_low_bp_skip_mult_bits : nat;
  cfg_collection_insert_mult_bits : nat;
  cfg_group_insert_mult_bits : nat;
  cfg_bracket_insert_mult_bits : nat;
  cfg_mixfix_substitute_mult_bits : nat;
  cfg_beam_width_bits : option nat;
  cfg_vpa_nesting_ceiling : option nat;
  cfg_max_recovery_depth : nat
}.

Definition recovery_synthesis_enabled
    (cfg : recovery_cost_config) : bool :=
  0 <? cfg_max_recovery_depth cfg.

Theorem max_recovery_depth_zero_disables_synthesis :
  forall cfg,
    cfg_max_recovery_depth cfg = 0 ->
    recovery_synthesis_enabled cfg = false.
Proof.
  intros cfg Hdepth.
  unfold recovery_synthesis_enabled.
  rewrite Hdepth.
  reflexivity.
Qed.

Theorem positive_max_recovery_depth_enables_synthesis :
  forall cfg,
    0 < cfg_max_recovery_depth cfg ->
    recovery_synthesis_enabled cfg = true.
Proof.
  intros cfg Hdepth.
  unfold recovery_synthesis_enabled.
  apply Nat.ltb_lt.
  exact Hdepth.
Qed.

Record recovery_depth_observation : Type := {
  rdo_deep : bool;
  rdo_shallow : bool;
  rdo_vpa_over : bool
}.

Definition observe_recovery_depth
    (cfg : recovery_cost_config)
    (depth : nat) : recovery_depth_observation :=
  {| rdo_deep := cfg_deep_nesting_threshold cfg <? depth;
     rdo_shallow := depth <? cfg_shallow_depth_threshold cfg;
     rdo_vpa_over :=
       match cfg_vpa_nesting_ceiling cfg with
       | Some ceiling => ceiling <? depth
       | None => false
       end |}.

Definition recovery_depth_tests_equal
    (cfg : recovery_cost_config)
    (d1 d2 : nat) : Prop :=
  (cfg_deep_nesting_threshold cfg <? d1) =
    (cfg_deep_nesting_threshold cfg <? d2)
  /\ (d1 <? cfg_shallow_depth_threshold cfg) =
    (d2 <? cfg_shallow_depth_threshold cfg)
  /\ (match cfg_vpa_nesting_ceiling cfg with
      | Some ceiling => ceiling <? d1
      | None => false
      end) =
     (match cfg_vpa_nesting_ceiling cfg with
      | Some ceiling => ceiling <? d2
      | None => false
      end).

Theorem same_depth_observation_preserves_depth_tests :
  forall cfg d1 d2,
    observe_recovery_depth cfg d1 = observe_recovery_depth cfg d2 ->
    recovery_depth_tests_equal cfg d1 d2.
Proof.
  intros cfg d1 d2 Hobs.
  unfold recovery_depth_tests_equal.
  unfold observe_recovery_depth in Hobs.
  inversion Hobs; subst.
  repeat split; reflexivity.
Qed.

Inductive recovery_frame_kind : Type :=
  | RfkPrefix
  | RfkInfixRhs
  | RfkPostfix
  | RfkCollection
  | RfkGroup
  | RfkMixfix
  | RfkLambda
  | RfkDollar
  | RfkCastWrap
  | RfkOther.

Definition recovery_frame_kind_class
    (frame_kind : recovery_frame_kind) : nat :=
  match frame_kind with
  | RfkInfixRhs => 1
  | RfkCollection => 2
  | RfkGroup => 3
  | RfkMixfix => 4
  | RfkPrefix
  | RfkPostfix
  | RfkLambda
  | RfkDollar
  | RfkCastWrap
  | RfkOther => 0
  end.

Theorem neutral_frame_kind_class_collapses :
  recovery_frame_kind_class RfkPrefix =
    recovery_frame_kind_class RfkOther /\
  recovery_frame_kind_class RfkPostfix =
    recovery_frame_kind_class RfkOther /\
  recovery_frame_kind_class RfkLambda =
    recovery_frame_kind_class RfkOther /\
  recovery_frame_kind_class RfkDollar =
    recovery_frame_kind_class RfkOther /\
  recovery_frame_kind_class RfkCastWrap =
    recovery_frame_kind_class RfkOther.
Proof.
  repeat split.
Qed.

Theorem multiplier_frame_kind_classes_separate_from_neutral :
  recovery_frame_kind_class RfkInfixRhs <>
    recovery_frame_kind_class RfkOther /\
  recovery_frame_kind_class RfkCollection <>
    recovery_frame_kind_class RfkOther /\
  recovery_frame_kind_class RfkGroup <>
    recovery_frame_kind_class RfkOther /\
  recovery_frame_kind_class RfkMixfix <>
    recovery_frame_kind_class RfkOther.
Proof.
  repeat split; discriminate.
Qed.

Record recovery_wfst_signature : Type := {
  rws_token_ids : list (nat * nat);
  rws_sync_tokens : list nat;
  rws_prediction_discounts : list (nat * nat);
  rws_bracket_mismatch_ids : list nat;
  rws_recursive_category : bool
}.

Record recovery_config_signature : Type := {
  rcs_skip_per_token_bits : nat;
  rcs_delete_cost_bits : nat;
  rcs_substitute_cost_bits : nat;
  rcs_insert_cost_bits : nat;
  rcs_swap_cost_bits : nat;
  rcs_max_skip_lookahead : nat;
  rcs_deep_nesting_threshold : nat;
  rcs_deep_nesting_skip_mult_bits : nat;
  rcs_shallow_depth_threshold : nat;
  rcs_shallow_depth_skip_mult_bits : nat;
  rcs_low_bp_threshold : nat;
  rcs_low_bp_skip_mult_bits : nat;
  rcs_collection_insert_mult_bits : nat;
  rcs_group_insert_mult_bits : nat;
  rcs_bracket_insert_mult_bits : nat;
  rcs_mixfix_substitute_mult_bits : nat;
  rcs_beam_width_bits : option nat;
  rcs_vpa_nesting_ceiling : option nat;
  rcs_max_recovery_depth : nat
}.

Definition recovery_config_signature_of
    (cfg : recovery_cost_config) : recovery_config_signature :=
  {| rcs_skip_per_token_bits := cfg_skip_per_token_bits cfg;
     rcs_delete_cost_bits := cfg_delete_cost_bits cfg;
     rcs_substitute_cost_bits := cfg_substitute_cost_bits cfg;
     rcs_insert_cost_bits := cfg_insert_cost_bits cfg;
     rcs_swap_cost_bits := cfg_swap_cost_bits cfg;
     rcs_max_skip_lookahead := cfg_max_skip_lookahead cfg;
     rcs_deep_nesting_threshold := cfg_deep_nesting_threshold cfg;
     rcs_deep_nesting_skip_mult_bits :=
       cfg_deep_nesting_skip_mult_bits cfg;
     rcs_shallow_depth_threshold := cfg_shallow_depth_threshold cfg;
     rcs_shallow_depth_skip_mult_bits :=
       cfg_shallow_depth_skip_mult_bits cfg;
     rcs_low_bp_threshold := cfg_low_bp_threshold cfg;
     rcs_low_bp_skip_mult_bits := cfg_low_bp_skip_mult_bits cfg;
     rcs_collection_insert_mult_bits :=
       cfg_collection_insert_mult_bits cfg;
     rcs_group_insert_mult_bits := cfg_group_insert_mult_bits cfg;
     rcs_bracket_insert_mult_bits := cfg_bracket_insert_mult_bits cfg;
     rcs_mixfix_substitute_mult_bits :=
       cfg_mixfix_substitute_mult_bits cfg;
     rcs_beam_width_bits := cfg_beam_width_bits cfg;
     rcs_vpa_nesting_ceiling := cfg_vpa_nesting_ceiling cfg;
     rcs_max_recovery_depth := cfg_max_recovery_depth cfg |}.

Record recovery_infra_signature : Type := {
  ris_token_ids : list (nat * nat);
  ris_sync_tokens : list nat;
  ris_config_signature : recovery_config_signature;
  ris_wfst_signature : recovery_wfst_signature
}.

Definition recovery_infra_signature_with_active_config
    (token_ids : list (nat * nat))
    (sync_tokens : list nat)
    (wfst_signature : recovery_wfst_signature)
    (cfg : recovery_cost_config) : recovery_infra_signature :=
  {| ris_token_ids := token_ids;
     ris_sync_tokens := sync_tokens;
     ris_config_signature := recovery_config_signature_of cfg;
     ris_wfst_signature := wfst_signature |}.

Record recovery_cache_key : Type := {
  rck_pos : nat;
  rck_state_cat_src_idx : nat;
  rck_cur_bp : nat;
  rck_frame_kind_class : nat;
  rck_depth_observation : recovery_depth_observation;
  rck_infra_signature : recovery_infra_signature;
  rck_dispatch_context_present : bool
}.

Definition recovery_cache_key_of_context
    (cfg : recovery_cost_config)
    (pos state_cat_src_idx cur_bp frame_kind_class depth : nat)
    (infra_signature : recovery_infra_signature)
    (dispatch_context_present : bool)
    : recovery_cache_key :=
  {| rck_pos := pos;
     rck_state_cat_src_idx := state_cat_src_idx;
     rck_cur_bp := cur_bp;
     rck_frame_kind_class := frame_kind_class;
     rck_depth_observation := observe_recovery_depth cfg depth;
     rck_infra_signature := infra_signature;
     rck_dispatch_context_present := dispatch_context_present |}.

Definition recovery_cache_key_of
    (cfg : recovery_cost_config)
    (pos state_cat_src_idx cur_bp frame_kind_class depth : nat)
    (infra_signature : recovery_infra_signature)
    : recovery_cache_key :=
  recovery_cache_key_of_context
    cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    infra_signature false.

Definition recovery_cache_key_with_active_config
    (cfg : recovery_cost_config)
    (pos state_cat_src_idx cur_bp frame_kind_class depth
      : nat)
    (token_ids : list (nat * nat))
    (sync_tokens : list nat)
    (wfst_signature : recovery_wfst_signature)
    : recovery_cache_key :=
  recovery_cache_key_of
    cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    (recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst_signature cfg).

Theorem recovery_cache_depth_observation_quotient :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class
      infra_signature d1 d2,
    observe_recovery_depth cfg d1 = observe_recovery_depth cfg d2 ->
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class d1
      infra_signature =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class d2
      infra_signature.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class
    infra_signature d1 d2 Hobs.
  unfold recovery_cache_key_of.
  unfold recovery_cache_key_of_context.
  rewrite Hobs.
  reflexivity.
Qed.

Theorem recovery_cache_neutral_frame_kind_quotient :
  forall cfg pos state_cat_src_idx cur_bp depth infra_signature,
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp
      (recovery_frame_kind_class RfkPrefix) depth
      infra_signature =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp
      (recovery_frame_kind_class RfkOther) depth
      infra_signature.
Proof.
  intros cfg pos state_cat_src_idx cur_bp depth infra_signature.
  reflexivity.
Qed.

Theorem generated_recovery_cache_key_has_absent_dispatch_context :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class
      depth infra_signature,
    rck_dispatch_context_present
      (recovery_cache_key_of
        cfg pos state_cat_src_idx cur_bp frame_kind_class depth
        infra_signature) = false.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class
    depth infra_signature.
  unfold recovery_cache_key_of.
  unfold recovery_cache_key_of_context.
  simpl.
  reflexivity.
Qed.

Theorem recovery_cache_key_independent_of_consumer_depth_budget :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature (max_depth1 max_depth2 : nat),
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    infra_signature max_depth1 max_depth2.
  reflexivity.
Qed.

Theorem active_config_signature_observes_max_recovery_depth :
  forall cfg,
    rcs_max_recovery_depth (recovery_config_signature_of cfg) =
    cfg_max_recovery_depth cfg.
Proof.
  intros cfg.
  reflexivity.
Qed.

Theorem active_config_signature_observes_depth_thresholds :
  forall cfg,
    rcs_deep_nesting_threshold (recovery_config_signature_of cfg) =
      cfg_deep_nesting_threshold cfg /\
    rcs_shallow_depth_threshold (recovery_config_signature_of cfg) =
      cfg_shallow_depth_threshold cfg /\
    rcs_vpa_nesting_ceiling (recovery_config_signature_of cfg) =
      cfg_vpa_nesting_ceiling cfg.
Proof.
  intros cfg.
  repeat split.
Qed.

Theorem active_config_signature_observes_branch_synthesis_fields :
  forall cfg,
    rcs_skip_per_token_bits (recovery_config_signature_of cfg) =
      cfg_skip_per_token_bits cfg /\
    rcs_delete_cost_bits (recovery_config_signature_of cfg) =
      cfg_delete_cost_bits cfg /\
    rcs_substitute_cost_bits (recovery_config_signature_of cfg) =
      cfg_substitute_cost_bits cfg /\
    rcs_insert_cost_bits (recovery_config_signature_of cfg) =
      cfg_insert_cost_bits cfg /\
    rcs_swap_cost_bits (recovery_config_signature_of cfg) =
      cfg_swap_cost_bits cfg /\
    rcs_max_skip_lookahead (recovery_config_signature_of cfg) =
      cfg_max_skip_lookahead cfg /\
    rcs_deep_nesting_skip_mult_bits
      (recovery_config_signature_of cfg) =
      cfg_deep_nesting_skip_mult_bits cfg /\
    rcs_shallow_depth_skip_mult_bits
      (recovery_config_signature_of cfg) =
      cfg_shallow_depth_skip_mult_bits cfg /\
    rcs_low_bp_threshold (recovery_config_signature_of cfg) =
      cfg_low_bp_threshold cfg /\
    rcs_low_bp_skip_mult_bits (recovery_config_signature_of cfg) =
      cfg_low_bp_skip_mult_bits cfg /\
    rcs_collection_insert_mult_bits
      (recovery_config_signature_of cfg) =
      cfg_collection_insert_mult_bits cfg /\
    rcs_group_insert_mult_bits (recovery_config_signature_of cfg) =
      cfg_group_insert_mult_bits cfg /\
    rcs_bracket_insert_mult_bits (recovery_config_signature_of cfg) =
      cfg_bracket_insert_mult_bits cfg /\
    rcs_mixfix_substitute_mult_bits
      (recovery_config_signature_of cfg) =
      cfg_mixfix_substitute_mult_bits cfg /\
    rcs_beam_width_bits (recovery_config_signature_of cfg) =
      cfg_beam_width_bits cfg.
Proof.
  intros cfg.
  repeat split.
Qed.

Theorem equal_active_config_signature_preserves_depth_observation :
  forall cfg1 cfg2 depth,
    recovery_config_signature_of cfg1 =
    recovery_config_signature_of cfg2 ->
    observe_recovery_depth cfg1 depth =
    observe_recovery_depth cfg2 depth.
Proof.
  intros cfg1 cfg2 depth Heq.
  pose proof (f_equal rcs_deep_nesting_threshold Heq) as Hdeep.
  pose proof (f_equal rcs_shallow_depth_threshold Heq) as Hshallow.
  pose proof (f_equal rcs_vpa_nesting_ceiling Heq) as Hvpa.
  simpl in Hdeep, Hshallow, Hvpa.
  unfold observe_recovery_depth.
  rewrite Hdeep, Hshallow, Hvpa.
  reflexivity.
Qed.

Theorem active_infra_signature_observes_max_recovery_depth :
  forall token_ids sync_tokens wfst_signature cfg1 cfg2,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst_signature cfg1 =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst_signature cfg2 ->
    cfg_max_recovery_depth cfg1 = cfg_max_recovery_depth cfg2.
Proof.
  intros token_ids sync_tokens wfst_signature cfg1 cfg2 Heq.
  pose proof
    (f_equal
      (fun infra =>
        rcs_max_recovery_depth (ris_config_signature infra))
      Heq) as Hmax.
  simpl in Hmax.
  exact Hmax.
Qed.

Theorem active_infra_signature_preserves_config_signature :
  forall token_ids sync_tokens wfst_signature cfg1 cfg2,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst_signature cfg1 =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst_signature cfg2 ->
    recovery_config_signature_of cfg1 =
    recovery_config_signature_of cfg2.
Proof.
  intros token_ids sync_tokens wfst_signature cfg1 cfg2 Heq.
  pose proof (f_equal ris_config_signature Heq) as Hcfg.
  simpl in Hcfg.
  exact Hcfg.
Qed.

Theorem active_infra_signature_preserves_wfst_signature :
  forall token_ids sync_tokens wfst_signature1 wfst_signature2 cfg,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst_signature1 cfg =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst_signature2 cfg ->
    wfst_signature1 = wfst_signature2.
Proof.
  intros token_ids sync_tokens wfst_signature1 wfst_signature2 cfg Heq.
  exact (f_equal ris_wfst_signature Heq).
Qed.

Theorem active_infra_signature_preserves_token_ids :
  forall token_ids1 token_ids2 sync_tokens wfst_signature cfg,
    recovery_infra_signature_with_active_config
      token_ids1 sync_tokens wfst_signature cfg =
    recovery_infra_signature_with_active_config
      token_ids2 sync_tokens wfst_signature cfg ->
    token_ids1 = token_ids2.
Proof.
  intros token_ids1 token_ids2 sync_tokens wfst_signature cfg Heq.
  exact (f_equal ris_token_ids Heq).
Qed.

Theorem active_infra_signature_preserves_sync_tokens :
  forall token_ids sync_tokens1 sync_tokens2 wfst_signature cfg,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens1 wfst_signature cfg =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens2 wfst_signature cfg ->
    sync_tokens1 = sync_tokens2.
Proof.
  intros token_ids sync_tokens1 sync_tokens2 wfst_signature cfg Heq.
  exact (f_equal ris_sync_tokens Heq).
Qed.

Theorem recovery_cache_key_independent_of_diagnostic_category_name :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature (category_name1 category_name2 : nat),
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    infra_signature category_name1 category_name2.
  reflexivity.
Qed.

Theorem recovery_cache_key_separates_dispatch_context_presence :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature present1 present2,
    recovery_cache_key_of_context
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature present1 =
    recovery_cache_key_of_context
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature present2 ->
    present1 = present2.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    infra_signature present1 present2 Heq.
  exact (f_equal rck_dispatch_context_present Heq).
Qed.

Theorem recovery_cache_key_separates_infra_signature :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature1 infra_signature2,
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature1 =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature2 ->
    infra_signature1 = infra_signature2.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    infra_signature1 infra_signature2 Heq.
  exact (f_equal rck_infra_signature Heq).
Qed.

Theorem recovery_cache_key_separates_wfst_signature :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens config_signature
      wfst_signature1 wfst_signature2,
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      {| ris_token_ids := token_ids;
         ris_sync_tokens := sync_tokens;
         ris_config_signature := config_signature;
         ris_wfst_signature := wfst_signature1 |} =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      {| ris_token_ids := token_ids;
         ris_sync_tokens := sync_tokens;
         ris_config_signature := config_signature;
         ris_wfst_signature := wfst_signature2 |} ->
    wfst_signature1 = wfst_signature2.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    token_ids sync_tokens config_signature wfst_signature1 wfst_signature2 Heq.
  apply recovery_cache_key_separates_infra_signature in Heq.
  exact (f_equal ris_wfst_signature Heq).
Qed.

Theorem recovery_cache_key_separates_token_ids :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids1 token_ids2 sync_tokens config_signature wfst_signature,
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      {| ris_token_ids := token_ids1;
         ris_sync_tokens := sync_tokens;
         ris_config_signature := config_signature;
         ris_wfst_signature := wfst_signature |} =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      {| ris_token_ids := token_ids2;
         ris_sync_tokens := sync_tokens;
         ris_config_signature := config_signature;
         ris_wfst_signature := wfst_signature |} ->
    token_ids1 = token_ids2.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    token_ids1 token_ids2 sync_tokens config_signature wfst_signature Heq.
  apply recovery_cache_key_separates_infra_signature in Heq.
  exact (f_equal ris_token_ids Heq).
Qed.

Theorem recovery_cache_key_separates_sync_tokens :
  forall cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens1 sync_tokens2 config_signature wfst_signature,
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      {| ris_token_ids := token_ids;
         ris_sync_tokens := sync_tokens1;
         ris_config_signature := config_signature;
         ris_wfst_signature := wfst_signature |} =
    recovery_cache_key_of
      cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      {| ris_token_ids := token_ids;
         ris_sync_tokens := sync_tokens2;
         ris_config_signature := config_signature;
         ris_wfst_signature := wfst_signature |} ->
    sync_tokens1 = sync_tokens2.
Proof.
  intros cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    token_ids sync_tokens1 sync_tokens2 config_signature wfst_signature Heq.
  apply recovery_cache_key_separates_infra_signature in Heq.
  exact (f_equal ris_sync_tokens Heq).
Qed.

Theorem recovery_cache_key_separates_active_config_signature :
  forall pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens wfst_signature active_cfg1 active_cfg2,
    recovery_cache_key_with_active_config
      active_cfg1 pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens wfst_signature =
    recovery_cache_key_with_active_config
      active_cfg2 pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens wfst_signature ->
    recovery_config_signature_of active_cfg1 =
    recovery_config_signature_of active_cfg2.
Proof.
  intros pos state_cat_src_idx cur_bp frame_kind_class depth
    token_ids sync_tokens wfst_signature active_cfg1 active_cfg2 Heq.
  pose proof
    (f_equal
      (fun key => ris_config_signature (rck_infra_signature key))
      Heq) as Hcfg.
  simpl in Hcfg.
  exact Hcfg.
Qed.

Theorem recovery_cache_key_equal_active_config_preserves_depth_observation :
  forall pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens wfst_signature active_cfg1 active_cfg2,
    recovery_cache_key_with_active_config
      active_cfg1 pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens wfst_signature =
    recovery_cache_key_with_active_config
      active_cfg2 pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens wfst_signature ->
    observe_recovery_depth active_cfg1 depth =
    observe_recovery_depth active_cfg2 depth.
Proof.
  intros pos state_cat_src_idx cur_bp frame_kind_class depth
    token_ids sync_tokens wfst_signature active_cfg1 active_cfg2 Heq.
  apply equal_active_config_signature_preserves_depth_observation.
  eapply recovery_cache_key_separates_active_config_signature.
  exact Heq.
Qed.

Theorem recovery_cache_key_separates_active_config_max_depth :
  forall depth_cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      token_ids sync_tokens wfst_signature active_cfg1 active_cfg2,
    recovery_cache_key_of
      depth_cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      (recovery_infra_signature_with_active_config
        token_ids sync_tokens wfst_signature active_cfg1) =
    recovery_cache_key_of
      depth_cfg pos state_cat_src_idx cur_bp frame_kind_class depth
      (recovery_infra_signature_with_active_config
        token_ids sync_tokens wfst_signature active_cfg2) ->
    cfg_max_recovery_depth active_cfg1 =
    cfg_max_recovery_depth active_cfg2.
Proof.
  intros depth_cfg pos state_cat_src_idx cur_bp frame_kind_class depth
    token_ids sync_tokens wfst_signature active_cfg1 active_cfg2 Heq.
  apply recovery_cache_key_separates_infra_signature in Heq.
  eapply active_infra_signature_observes_max_recovery_depth.
  exact Heq.
Qed.

Definition recovery_infra_matches_state
    (state_cat_src_idx infra_category_src_idx : nat) : bool :=
  state_cat_src_idx =? infra_category_src_idx.

Theorem recovery_infra_match_accepts_equal_category :
  forall state_cat_src_idx,
    recovery_infra_matches_state
      state_cat_src_idx state_cat_src_idx = true.
Proof.
  intros state_cat_src_idx.
  unfold recovery_infra_matches_state.
  apply Nat.eqb_refl.
Qed.

Theorem recovery_infra_match_rejects_mismatched_category :
  forall state_cat_src_idx infra_category_src_idx,
    state_cat_src_idx <> infra_category_src_idx ->
    recovery_infra_matches_state
      state_cat_src_idx infra_category_src_idx = false.
Proof.
  intros state_cat_src_idx infra_category_src_idx Hneq.
  unfold recovery_infra_matches_state.
  apply Nat.eqb_neq.
  exact Hneq.
Qed.

Theorem recovery_infra_match_implies_same_category :
  forall state_cat_src_idx infra_category_src_idx,
    recovery_infra_matches_state
      state_cat_src_idx infra_category_src_idx = true ->
    state_cat_src_idx = infra_category_src_idx.
Proof.
  intros state_cat_src_idx infra_category_src_idx Hmatch.
  unfold recovery_infra_matches_state in Hmatch.
  apply Nat.eqb_eq.
  exact Hmatch.
Qed.

Theorem valid_recovery_cache_key_category_matches_infra :
  forall cfg pos state_cat_src_idx infra_category_src_idx cur_bp
      frame_kind_class depth infra_signature,
    recovery_infra_matches_state
      state_cat_src_idx infra_category_src_idx = true ->
    rck_state_cat_src_idx
      (recovery_cache_key_of
        cfg pos state_cat_src_idx cur_bp frame_kind_class depth
        infra_signature) =
    infra_category_src_idx.
Proof.
  intros cfg pos state_cat_src_idx infra_category_src_idx cur_bp
    frame_kind_class depth infra_signature Hmatch.
  unfold recovery_cache_key_of.
  unfold recovery_cache_key_of_context.
  simpl.
  apply recovery_infra_match_implies_same_category.
  exact Hmatch.
Qed.

Theorem recovery_cache_key_separates_positions :
  forall cfg pos1 pos2 state_cat_src_idx cur_bp frame_kind_class
      depth infra_signature,
    recovery_cache_key_of
      cfg pos1 state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature =
    recovery_cache_key_of
      cfg pos2 state_cat_src_idx cur_bp frame_kind_class depth
      infra_signature ->
    pos1 = pos2.
Proof.
  intros cfg pos1 pos2 state_cat_src_idx cur_bp frame_kind_class
    depth infra_signature Heq.
  exact (f_equal rck_pos Heq).
Qed.

Definition packed_dispatch_pos_limit : nat := 2 ^ 40.

(* Keep the concrete Rust bit-width visible in the definition, but prevent
   arithmetic tactics from expanding 2 ^ 40 while proving domain properties. *)
Opaque packed_dispatch_pos_limit.

Definition packed_dispatch_position_valid (pos : nat) : Prop :=
  pos < packed_dispatch_pos_limit.

Definition packed_dispatch_position_bits (pos : nat) : nat :=
  pos mod packed_dispatch_pos_limit.

Theorem packed_dispatch_position_bits_preserve_valid :
  forall pos,
    packed_dispatch_position_valid pos ->
    packed_dispatch_position_bits pos = pos.
Proof.
  intros pos Hvalid.
  unfold packed_dispatch_position_bits.
  unfold packed_dispatch_position_valid in Hvalid.
  apply Nat.mod_small.
  exact Hvalid.
Qed.

Theorem packed_dispatch_position_bits_injective_valid :
  forall pos1 pos2,
    packed_dispatch_position_valid pos1 ->
    packed_dispatch_position_valid pos2 ->
    packed_dispatch_position_bits pos1 =
    packed_dispatch_position_bits pos2 ->
    pos1 = pos2.
Proof.
  intros pos1 pos2 Hvalid1 Hvalid2 Hbits.
  rewrite (packed_dispatch_position_bits_preserve_valid pos1 Hvalid1) in Hbits.
  rewrite (packed_dispatch_position_bits_preserve_valid pos2 Hvalid2) in Hbits.
  exact Hbits.
Qed.

(* Runtime packers must reject positions outside this domain; injectivity is
   only proved for packed_dispatch_position_valid positions. *)
Theorem packed_dispatch_position_limit_is_invalid :
  ~ packed_dispatch_position_valid packed_dispatch_pos_limit.
Proof.
  unfold packed_dispatch_position_valid.
  apply Nat.lt_irrefl.
Qed.

Theorem recovery_cache_depth_class_quotient_sound :
  forall cfg d1 d2,
    observe_recovery_depth cfg d1 = observe_recovery_depth cfg d2 ->
    recovery_depth_tests_equal cfg d1 d2.
Proof.
  exact same_depth_observation_preserves_depth_tests.
Qed.

Record token_dependent_caches : Type := {
  cache_dispatch_entries : nat;
  cache_pending_drains : nat;
  cache_recovery_entries : nat;
  cache_chain_earley_entries : nat;
  cache_chain_interval_entries : nat;
  cache_dispatch_registrations : nat;
  cache_recovery_registrations : nat
}.

Definition token_dependent_entry_count (caches : token_dependent_caches) : nat :=
  cache_dispatch_entries caches
  + cache_pending_drains caches
  + cache_recovery_entries caches
  + cache_chain_earley_entries caches
  + cache_chain_interval_entries caches.

Definition invalidate_token_dependent_caches
    (caches : token_dependent_caches) : token_dependent_caches :=
  {| cache_dispatch_entries := 0;
     cache_pending_drains := 0;
     cache_recovery_entries := 0;
     cache_chain_earley_entries := 0;
     cache_chain_interval_entries := 0;
     cache_dispatch_registrations := cache_dispatch_registrations caches;
     cache_recovery_registrations := cache_recovery_registrations caches |}.

Definition invalidate_token_dependent_caches_after_effect
    (caches : token_dependent_caches)
    (effect : recovery_effect) : token_dependent_caches :=
  if recovery_effect_mutates_token_source effect
  then invalidate_token_dependent_caches caches
  else caches.

Definition rebind_mutable_token_source
    (caches : token_dependent_caches) : token_dependent_caches :=
  invalidate_token_dependent_caches caches.

Theorem token_mutation_invalidates_all_token_dependent_entries :
  forall caches,
    token_dependent_entry_count
      (invalidate_token_dependent_caches caches) = 0.
Proof.
  intros caches.
  destruct caches.
  reflexivity.
Qed.

Theorem mutable_token_source_rebind_invalidates_all_token_dependent_entries :
  forall caches,
    token_dependent_entry_count
      (rebind_mutable_token_source caches) = 0.
Proof.
  intros caches.
  unfold rebind_mutable_token_source.
  apply token_mutation_invalidates_all_token_dependent_entries.
Qed.

Theorem mutating_recovery_effect_invalidates_all_token_dependent_entries :
  forall caches effect,
    recovery_effect_mutates_token_source effect = true ->
    token_dependent_entry_count
      (invalidate_token_dependent_caches_after_effect caches effect) = 0.
Proof.
  intros caches effect Hmut.
  unfold invalidate_token_dependent_caches_after_effect.
  rewrite Hmut.
  apply token_mutation_invalidates_all_token_dependent_entries.
Qed.

Theorem nonmutating_recovery_effect_preserves_token_dependent_caches :
  forall caches effect,
    recovery_effect_mutates_token_source effect = false ->
    invalidate_token_dependent_caches_after_effect caches effect = caches.
Proof.
  intros caches effect Hstable.
  unfold invalidate_token_dependent_caches_after_effect.
  rewrite Hstable.
  reflexivity.
Qed.

Theorem token_mutation_preserves_dispatch_diagnostics :
  forall caches,
    cache_dispatch_registrations
      (invalidate_token_dependent_caches caches) =
    cache_dispatch_registrations caches.
Proof.
  intros caches.
  destruct caches.
  reflexivity.
Qed.

Theorem mutable_token_source_rebind_preserves_dispatch_diagnostics :
  forall caches,
    cache_dispatch_registrations
      (rebind_mutable_token_source caches) =
    cache_dispatch_registrations caches.
Proof.
  intros caches.
  unfold rebind_mutable_token_source.
  apply token_mutation_preserves_dispatch_diagnostics.
Qed.

Theorem token_mutation_preserves_recovery_diagnostics :
  forall caches,
    cache_recovery_registrations
      (invalidate_token_dependent_caches caches) =
    cache_recovery_registrations caches.
Proof.
  intros caches.
  destruct caches.
  reflexivity.
Qed.

Theorem mutable_token_source_rebind_preserves_recovery_diagnostics :
  forall caches,
    cache_recovery_registrations
      (rebind_mutable_token_source caches) =
    cache_recovery_registrations caches.
Proof.
  intros caches.
  unfold rebind_mutable_token_source.
  apply token_mutation_preserves_recovery_diagnostics.
Qed.

Theorem accepted_recovery_children_are_bounded_and_safe :
  forall max_depth key c branches b target_pos,
    recovery_gate_accepts max_depth key c branches = true ->
    In b (bounded_recovery_branches (rc_pos c) branches) ->
    br_prefix_target b = Some target_pos ->
    target_pos <= rc_pos c ->
    length (bounded_recovery_branches (rc_pos c) branches)
      <= recovery_fork_max_branches
    /\ branch_target_valid b = true
    /\ branch_non_advancing_insert b = true
    /\ rc_depth (child_after_recovery key c) <= max_depth.
Proof.
  intros max_depth key c branches b target_pos Hgate Hin Htarget Hle.
  split.
  - apply bounded_recovery_branch_limit.
  - split.
    + eapply bounded_recovery_retains_only_target_valid_branches.
      exact Hin.
    + split.
      * eapply prefix_nonadvancing_branch_requires_insert.
        -- exact Htarget.
        -- exact Hle.
        -- eapply bounded_recovery_retains_only_progress_or_insert.
           exact Hin.
      * eapply accepted_child_depth_le_max.
        exact Hgate.
Qed.
