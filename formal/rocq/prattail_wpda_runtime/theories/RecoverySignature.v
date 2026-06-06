(*
 * RecoverySignature: cache-key obligations for recovery-dispatch cohort
 * sharing.
 *
 * The Rust cache key includes an exact finite observation of the active
 * RecoveryConfig and RecoveryInfra. These lemmas record the projection facts
 * that make cache reuse sound with respect to recovery branch synthesis.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From PrattailWpdaRuntime Require RecoveryBound.

Import ListNotations.

Record recovery_config : Type := {
  rc_skip_per_token_bits : nat;
  rc_delete_cost_bits : nat;
  rc_substitute_cost_bits : nat;
  rc_insert_cost_bits : nat;
  rc_swap_cost_bits : nat;
  rc_max_skip_lookahead : nat;
  rc_deep_nesting_threshold : nat;
  rc_deep_nesting_skip_mult_bits : nat;
  rc_shallow_depth_threshold : nat;
  rc_shallow_depth_skip_mult_bits : nat;
  rc_low_bp_threshold : nat;
  rc_low_bp_skip_mult_bits : nat;
  rc_collection_insert_mult_bits : nat;
  rc_group_insert_mult_bits : nat;
  rc_bracket_insert_mult_bits : nat;
  rc_mixfix_substitute_mult_bits : nat;
  rc_beam_width_bits : option nat;
  rc_vpa_nesting_ceiling : option nat;
  rc_max_recovery_depth : nat
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
    (cfg : recovery_config) : recovery_config_signature :=
  {| rcs_skip_per_token_bits := rc_skip_per_token_bits cfg;
     rcs_delete_cost_bits := rc_delete_cost_bits cfg;
     rcs_substitute_cost_bits := rc_substitute_cost_bits cfg;
     rcs_insert_cost_bits := rc_insert_cost_bits cfg;
     rcs_swap_cost_bits := rc_swap_cost_bits cfg;
     rcs_max_skip_lookahead := rc_max_skip_lookahead cfg;
     rcs_deep_nesting_threshold := rc_deep_nesting_threshold cfg;
     rcs_deep_nesting_skip_mult_bits := rc_deep_nesting_skip_mult_bits cfg;
     rcs_shallow_depth_threshold := rc_shallow_depth_threshold cfg;
     rcs_shallow_depth_skip_mult_bits := rc_shallow_depth_skip_mult_bits cfg;
     rcs_low_bp_threshold := rc_low_bp_threshold cfg;
     rcs_low_bp_skip_mult_bits := rc_low_bp_skip_mult_bits cfg;
     rcs_collection_insert_mult_bits := rc_collection_insert_mult_bits cfg;
     rcs_group_insert_mult_bits := rc_group_insert_mult_bits cfg;
     rcs_bracket_insert_mult_bits := rc_bracket_insert_mult_bits cfg;
     rcs_mixfix_substitute_mult_bits := rc_mixfix_substitute_mult_bits cfg;
     rcs_beam_width_bits := rc_beam_width_bits cfg;
     rcs_vpa_nesting_ceiling := rc_vpa_nesting_ceiling cfg;
     rcs_max_recovery_depth := rc_max_recovery_depth cfg |}.

Record recovery_depth_observation : Type := {
  rdo_deep : bool;
  rdo_shallow : bool;
  rdo_vpa_over : bool
}.

Definition observe_recovery_depth
    (cfg : recovery_config)
    (depth : nat) : recovery_depth_observation :=
  {| rdo_deep := rc_deep_nesting_threshold cfg <? depth;
     rdo_shallow := depth <? rc_shallow_depth_threshold cfg;
     rdo_vpa_over :=
       match rc_vpa_nesting_ceiling cfg with
       | Some ceiling => ceiling <? depth
       | None => false
       end |}.

Theorem active_config_signature_observes_max_recovery_depth :
  forall cfg,
    rcs_max_recovery_depth (recovery_config_signature_of cfg) =
    rc_max_recovery_depth cfg.
Proof.
  intros cfg.
  reflexivity.
Qed.

Theorem active_config_signature_observes_depth_thresholds :
  forall cfg,
    rcs_deep_nesting_threshold (recovery_config_signature_of cfg) =
      rc_deep_nesting_threshold cfg /\
    rcs_shallow_depth_threshold (recovery_config_signature_of cfg) =
      rc_shallow_depth_threshold cfg /\
    rcs_vpa_nesting_ceiling (recovery_config_signature_of cfg) =
      rc_vpa_nesting_ceiling cfg.
Proof.
  intros cfg.
  repeat split.
Qed.

Theorem active_config_signature_observes_branch_synthesis_fields :
  forall cfg,
    rcs_skip_per_token_bits (recovery_config_signature_of cfg) =
      rc_skip_per_token_bits cfg /\
    rcs_delete_cost_bits (recovery_config_signature_of cfg) =
      rc_delete_cost_bits cfg /\
    rcs_substitute_cost_bits (recovery_config_signature_of cfg) =
      rc_substitute_cost_bits cfg /\
    rcs_insert_cost_bits (recovery_config_signature_of cfg) =
      rc_insert_cost_bits cfg /\
    rcs_swap_cost_bits (recovery_config_signature_of cfg) =
      rc_swap_cost_bits cfg /\
    rcs_max_skip_lookahead (recovery_config_signature_of cfg) =
      rc_max_skip_lookahead cfg /\
    rcs_deep_nesting_skip_mult_bits (recovery_config_signature_of cfg) =
      rc_deep_nesting_skip_mult_bits cfg /\
    rcs_shallow_depth_skip_mult_bits (recovery_config_signature_of cfg) =
      rc_shallow_depth_skip_mult_bits cfg /\
    rcs_low_bp_threshold (recovery_config_signature_of cfg) =
      rc_low_bp_threshold cfg /\
    rcs_low_bp_skip_mult_bits (recovery_config_signature_of cfg) =
      rc_low_bp_skip_mult_bits cfg /\
    rcs_collection_insert_mult_bits (recovery_config_signature_of cfg) =
      rc_collection_insert_mult_bits cfg /\
    rcs_group_insert_mult_bits (recovery_config_signature_of cfg) =
      rc_group_insert_mult_bits cfg /\
    rcs_bracket_insert_mult_bits (recovery_config_signature_of cfg) =
      rc_bracket_insert_mult_bits cfg /\
    rcs_mixfix_substitute_mult_bits (recovery_config_signature_of cfg) =
      rc_mixfix_substitute_mult_bits cfg /\
    rcs_beam_width_bits (recovery_config_signature_of cfg) =
      rc_beam_width_bits cfg.
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
  intros cfg1 cfg2 depth Hsig.
  pose proof (f_equal rcs_deep_nesting_threshold Hsig) as Hdeep.
  pose proof (f_equal rcs_shallow_depth_threshold Hsig) as Hshallow.
  pose proof (f_equal rcs_vpa_nesting_ceiling Hsig) as Hvpa.
  simpl in Hdeep, Hshallow, Hvpa.
  unfold observe_recovery_depth.
  rewrite Hdeep, Hshallow, Hvpa.
  reflexivity.
Qed.

Record recovery_wfst_signature : Type := {
  rws_token_ids : list (nat * nat);
  rws_sync_tokens : list nat;
  rws_prediction_discounts : list (nat * nat);
  rws_bracket_mismatch_ids : list nat;
  rws_recursive_category : bool
}.

Record recovery_infra_signature : Type := {
  ris_token_ids : list (nat * nat);
  ris_sync_tokens : list nat;
  ris_config : recovery_config_signature;
  ris_wfst : recovery_wfst_signature
}.

Definition recovery_infra_signature_with_active_config
    (token_ids : list (nat * nat))
    (sync_tokens : list nat)
    (wfst : recovery_wfst_signature)
    (cfg : recovery_config) : recovery_infra_signature :=
  {| ris_token_ids := token_ids;
     ris_sync_tokens := sync_tokens;
     ris_config := recovery_config_signature_of cfg;
     ris_wfst := wfst |}.

Definition recovery_bound_config_of
    (cfg : recovery_config) : RecoveryBound.recovery_cost_config :=
  {| RecoveryBound.cfg_skip_per_token_bits := rc_skip_per_token_bits cfg;
     RecoveryBound.cfg_delete_cost_bits := rc_delete_cost_bits cfg;
     RecoveryBound.cfg_substitute_cost_bits :=
       rc_substitute_cost_bits cfg;
     RecoveryBound.cfg_insert_cost_bits := rc_insert_cost_bits cfg;
     RecoveryBound.cfg_swap_cost_bits := rc_swap_cost_bits cfg;
     RecoveryBound.cfg_max_skip_lookahead := rc_max_skip_lookahead cfg;
     RecoveryBound.cfg_deep_nesting_threshold :=
       rc_deep_nesting_threshold cfg;
     RecoveryBound.cfg_deep_nesting_skip_mult_bits :=
       rc_deep_nesting_skip_mult_bits cfg;
     RecoveryBound.cfg_shallow_depth_threshold :=
       rc_shallow_depth_threshold cfg;
     RecoveryBound.cfg_shallow_depth_skip_mult_bits :=
       rc_shallow_depth_skip_mult_bits cfg;
     RecoveryBound.cfg_low_bp_threshold := rc_low_bp_threshold cfg;
     RecoveryBound.cfg_low_bp_skip_mult_bits :=
       rc_low_bp_skip_mult_bits cfg;
     RecoveryBound.cfg_collection_insert_mult_bits :=
       rc_collection_insert_mult_bits cfg;
     RecoveryBound.cfg_group_insert_mult_bits :=
       rc_group_insert_mult_bits cfg;
     RecoveryBound.cfg_bracket_insert_mult_bits :=
       rc_bracket_insert_mult_bits cfg;
     RecoveryBound.cfg_mixfix_substitute_mult_bits :=
       rc_mixfix_substitute_mult_bits cfg;
     RecoveryBound.cfg_beam_width_bits := rc_beam_width_bits cfg;
     RecoveryBound.cfg_vpa_nesting_ceiling := rc_vpa_nesting_ceiling cfg;
     RecoveryBound.cfg_max_recovery_depth := rc_max_recovery_depth cfg |}.

Definition recovery_bound_config_signature_of
    (sig : recovery_config_signature)
    : RecoveryBound.recovery_config_signature :=
  {| RecoveryBound.rcs_skip_per_token_bits :=
       rcs_skip_per_token_bits sig;
     RecoveryBound.rcs_delete_cost_bits := rcs_delete_cost_bits sig;
     RecoveryBound.rcs_substitute_cost_bits :=
       rcs_substitute_cost_bits sig;
     RecoveryBound.rcs_insert_cost_bits := rcs_insert_cost_bits sig;
     RecoveryBound.rcs_swap_cost_bits := rcs_swap_cost_bits sig;
     RecoveryBound.rcs_max_skip_lookahead :=
       rcs_max_skip_lookahead sig;
     RecoveryBound.rcs_deep_nesting_threshold :=
       rcs_deep_nesting_threshold sig;
     RecoveryBound.rcs_deep_nesting_skip_mult_bits :=
       rcs_deep_nesting_skip_mult_bits sig;
     RecoveryBound.rcs_shallow_depth_threshold :=
       rcs_shallow_depth_threshold sig;
     RecoveryBound.rcs_shallow_depth_skip_mult_bits :=
       rcs_shallow_depth_skip_mult_bits sig;
     RecoveryBound.rcs_low_bp_threshold := rcs_low_bp_threshold sig;
     RecoveryBound.rcs_low_bp_skip_mult_bits :=
       rcs_low_bp_skip_mult_bits sig;
     RecoveryBound.rcs_collection_insert_mult_bits :=
       rcs_collection_insert_mult_bits sig;
     RecoveryBound.rcs_group_insert_mult_bits :=
       rcs_group_insert_mult_bits sig;
     RecoveryBound.rcs_bracket_insert_mult_bits :=
       rcs_bracket_insert_mult_bits sig;
     RecoveryBound.rcs_mixfix_substitute_mult_bits :=
       rcs_mixfix_substitute_mult_bits sig;
     RecoveryBound.rcs_beam_width_bits := rcs_beam_width_bits sig;
     RecoveryBound.rcs_vpa_nesting_ceiling :=
       rcs_vpa_nesting_ceiling sig;
     RecoveryBound.rcs_max_recovery_depth :=
       rcs_max_recovery_depth sig |}.

Definition recovery_bound_depth_observation_of
    (obs : recovery_depth_observation)
    : RecoveryBound.recovery_depth_observation :=
  {| RecoveryBound.rdo_deep := rdo_deep obs;
     RecoveryBound.rdo_shallow := rdo_shallow obs;
     RecoveryBound.rdo_vpa_over := rdo_vpa_over obs |}.

Definition recovery_bound_wfst_signature_of
    (wfst : recovery_wfst_signature)
    : RecoveryBound.recovery_wfst_signature :=
  {| RecoveryBound.rws_token_ids := rws_token_ids wfst;
     RecoveryBound.rws_sync_tokens := rws_sync_tokens wfst;
     RecoveryBound.rws_prediction_discounts :=
       rws_prediction_discounts wfst;
     RecoveryBound.rws_bracket_mismatch_ids :=
       rws_bracket_mismatch_ids wfst;
     RecoveryBound.rws_recursive_category := rws_recursive_category wfst |}.

Definition recovery_bound_infra_signature_of
    (infra : recovery_infra_signature)
    : RecoveryBound.recovery_infra_signature :=
  {| RecoveryBound.ris_token_ids := ris_token_ids infra;
     RecoveryBound.ris_sync_tokens := ris_sync_tokens infra;
     RecoveryBound.ris_config_signature :=
       recovery_bound_config_signature_of (ris_config infra);
     RecoveryBound.ris_wfst_signature :=
       recovery_bound_wfst_signature_of (ris_wfst infra) |}.

Theorem recovery_config_signature_matches_recovery_bound :
  forall cfg,
    recovery_bound_config_signature_of
      (recovery_config_signature_of cfg) =
    RecoveryBound.recovery_config_signature_of
      (recovery_bound_config_of cfg).
Proof.
  intros cfg.
  destruct cfg.
  reflexivity.
Qed.

Theorem recovery_depth_observation_matches_recovery_bound :
  forall cfg depth,
    recovery_bound_depth_observation_of
      (observe_recovery_depth cfg depth) =
    RecoveryBound.observe_recovery_depth
      (recovery_bound_config_of cfg) depth.
Proof.
  intros cfg depth.
  destruct cfg.
  reflexivity.
Qed.

Theorem recovery_infra_signature_matches_recovery_bound :
  forall token_ids sync_tokens wfst cfg,
    recovery_bound_infra_signature_of
      (recovery_infra_signature_with_active_config
        token_ids sync_tokens wfst cfg) =
    RecoveryBound.recovery_infra_signature_with_active_config
      token_ids
      sync_tokens
      (recovery_bound_wfst_signature_of wfst)
      (recovery_bound_config_of cfg).
Proof.
  intros token_ids sync_tokens wfst cfg.
  unfold recovery_bound_infra_signature_of.
  simpl.
  rewrite recovery_config_signature_matches_recovery_bound.
  reflexivity.
Qed.

Theorem active_infra_signature_eq_preserves_config_signature :
  forall token_ids sync_tokens wfst cfg1 cfg2,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst cfg1 =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst cfg2 ->
    recovery_config_signature_of cfg1 =
    recovery_config_signature_of cfg2.
Proof.
  intros token_ids sync_tokens wfst cfg1 cfg2 Hsig.
  exact (f_equal ris_config Hsig).
Qed.

Theorem active_infra_signature_eq_preserves_max_recovery_depth :
  forall token_ids sync_tokens wfst cfg1 cfg2,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst cfg1 =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst cfg2 ->
    rc_max_recovery_depth cfg1 = rc_max_recovery_depth cfg2.
Proof.
  intros token_ids sync_tokens wfst cfg1 cfg2 Hsig.
  pose proof
    (active_infra_signature_eq_preserves_config_signature
      token_ids sync_tokens wfst cfg1 cfg2 Hsig) as Hcfg.
  assert
    (rcs_max_recovery_depth (recovery_config_signature_of cfg1) =
     rcs_max_recovery_depth (recovery_config_signature_of cfg2)) as Hmax.
  { now rewrite Hcfg. }
  exact Hmax.
Qed.

Theorem active_infra_signature_eq_preserves_wfst_signature :
  forall token_ids sync_tokens wfst1 wfst2 cfg,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst1 cfg =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens wfst2 cfg ->
    wfst1 = wfst2.
Proof.
  intros token_ids sync_tokens wfst1 wfst2 cfg Hsig.
  exact (f_equal ris_wfst Hsig).
Qed.

Theorem active_infra_signature_eq_preserves_token_ids :
  forall token_ids1 token_ids2 sync_tokens wfst cfg,
    recovery_infra_signature_with_active_config
      token_ids1 sync_tokens wfst cfg =
    recovery_infra_signature_with_active_config
      token_ids2 sync_tokens wfst cfg ->
    token_ids1 = token_ids2.
Proof.
  intros token_ids1 token_ids2 sync_tokens wfst cfg Hsig.
  exact (f_equal ris_token_ids Hsig).
Qed.

Theorem active_infra_signature_eq_preserves_sync_tokens :
  forall token_ids sync_tokens1 sync_tokens2 wfst cfg,
    recovery_infra_signature_with_active_config
      token_ids sync_tokens1 wfst cfg =
    recovery_infra_signature_with_active_config
      token_ids sync_tokens2 wfst cfg ->
    sync_tokens1 = sync_tokens2.
Proof.
  intros token_ids sync_tokens1 sync_tokens2 wfst cfg Hsig.
  exact (f_equal ris_sync_tokens Hsig).
Qed.

Record token_dependent_cache_state : Type := {
  tcs_dispatch_cohort : bool;
  tcs_pending_drain_keys : bool;
  tcs_recovery_cohort : bool;
  tcs_chain_earley : bool;
  tcs_chain_absorbed_intervals : bool;
  tcs_dispatch_registrations : nat;
  tcs_recovery_registrations : nat
}.

Definition token_dependent_caches_cleared
    (state : token_dependent_cache_state) : bool :=
  negb (tcs_dispatch_cohort state) &&
  negb (tcs_pending_drain_keys state) &&
  negb (tcs_recovery_cohort state) &&
  negb (tcs_chain_earley state) &&
  negb (tcs_chain_absorbed_intervals state).

Definition invalidate_token_dependent_caches
    (state : token_dependent_cache_state) : token_dependent_cache_state :=
  {| tcs_dispatch_cohort := false;
     tcs_pending_drain_keys := false;
     tcs_recovery_cohort := false;
     tcs_chain_earley := false;
     tcs_chain_absorbed_intervals := false;
     tcs_dispatch_registrations := tcs_dispatch_registrations state;
     tcs_recovery_registrations := tcs_recovery_registrations state |}.

Definition replay_cache_state_after
    (effect : RecoveryBound.recovery_effect)
    (state : token_dependent_cache_state) : token_dependent_cache_state :=
  if RecoveryBound.recovery_effect_mutates_token_source effect
  then invalidate_token_dependent_caches state
  else state.

Definition rebind_cache_state_after
    (state : token_dependent_cache_state) : token_dependent_cache_state :=
  invalidate_token_dependent_caches state.

Theorem mutating_recovery_replay_clears_token_dependent_caches :
  forall effect state,
    RecoveryBound.recovery_effect_mutates_token_source effect = true ->
    token_dependent_caches_cleared
      (replay_cache_state_after effect state) = true.
Proof.
  intros effect state Hmut.
  unfold replay_cache_state_after.
  rewrite Hmut.
  reflexivity.
Qed.

Theorem mutable_token_source_rebind_clears_token_dependent_caches :
  forall state,
    token_dependent_caches_cleared
      (rebind_cache_state_after state) = true.
Proof.
  intros state.
  unfold rebind_cache_state_after.
  reflexivity.
Qed.

Theorem nonmutating_recovery_replay_preserves_token_dependent_caches :
  forall effect state,
    RecoveryBound.recovery_effect_mutates_token_source effect = false ->
    replay_cache_state_after effect state = state.
Proof.
  intros effect state Hmut.
  unfold replay_cache_state_after.
  rewrite Hmut.
  reflexivity.
Qed.

Theorem token_mutation_preserves_dispatch_diagnostics :
  forall state,
    tcs_dispatch_registrations
      (invalidate_token_dependent_caches state) =
    tcs_dispatch_registrations state.
Proof.
  intros state.
  destruct state.
  reflexivity.
Qed.

Theorem token_mutation_preserves_recovery_diagnostics :
  forall state,
    tcs_recovery_registrations
      (invalidate_token_dependent_caches state) =
    tcs_recovery_registrations state.
Proof.
  intros state.
  destruct state.
  reflexivity.
Qed.

Theorem mutable_token_source_rebind_preserves_dispatch_diagnostics :
  forall state,
    tcs_dispatch_registrations
      (rebind_cache_state_after state) =
    tcs_dispatch_registrations state.
Proof.
  intros state.
  unfold rebind_cache_state_after.
  apply token_mutation_preserves_dispatch_diagnostics.
Qed.

Theorem mutable_token_source_rebind_preserves_recovery_diagnostics :
  forall state,
    tcs_recovery_registrations
      (rebind_cache_state_after state) =
    tcs_recovery_registrations state.
Proof.
  intros state.
  unfold rebind_cache_state_after.
  apply token_mutation_preserves_recovery_diagnostics.
Qed.

Inductive walker_step_driver : Type :=
  | DriverProcessEvent
  | DriverRunToCompletion
  | DriverRunToSaturation
  | DriverRunToEndOfInput
  | DriverRunWithObservedConsumer.

Record recovery_pin_scope : Type := {
  rps_cache_pinned : bool;
  rps_config_pinned : bool
}.

Definition driver_recovery_pin_scope
    (_driver : walker_step_driver) : recovery_pin_scope :=
  {| rps_cache_pinned := true;
     rps_config_pinned := true |}.

Definition generated_recovery_config_source
    (scope : recovery_pin_scope)
    (active_config infra_default : recovery_config)
    : recovery_config :=
  if rps_config_pinned scope then active_config else infra_default.

Theorem all_walker_step_drivers_pin_recovery_cache_and_config :
  forall driver,
    rps_cache_pinned (driver_recovery_pin_scope driver) = true /\
    rps_config_pinned (driver_recovery_pin_scope driver) = true.
Proof.
  intros driver.
  destruct driver; simpl; split; reflexivity.
Qed.

Theorem pinned_driver_uses_active_recovery_config :
  forall driver active_config infra_default,
    generated_recovery_config_source
      (driver_recovery_pin_scope driver)
      active_config
      infra_default = active_config.
Proof.
  intros driver active_config infra_default.
  destruct driver; reflexivity.
Qed.

Theorem pinned_driver_exposes_recovery_cache :
  forall driver,
    rps_cache_pinned (driver_recovery_pin_scope driver) = true.
Proof.
  intros driver.
  destruct driver; reflexivity.
Qed.

Example insert_sequence_mutates_token_source :
  RecoveryBound.recovery_effect_mutates_token_source
    (RecoveryBound.DeltaApplyRecoverySequence
      0 [RecoveryBound.ResolvedInsertToken]) = true.
Proof. reflexivity. Qed.

Example cursor_only_sequence_does_not_mutate_token_source :
  RecoveryBound.recovery_effect_mutates_token_source
    (RecoveryBound.DeltaApplyRecoverySequence
      2 [RecoveryBound.ResolvedDeleteToken;
         RecoveryBound.ResolvedSkipToSync]) = false.
Proof. reflexivity. Qed.
